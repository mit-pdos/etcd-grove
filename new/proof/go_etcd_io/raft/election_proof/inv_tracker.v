(** * The progress tracker and per-peer progress

    Since 2026-09-16 these are **definitions, not axioms**.  The tracker is
    core raft, so it is in scope: the only things this development is allowed
    to assume outright are the ones outside the raft protocol itself (the
    [Logger] interface, the tracing hooks, [slices.Sort], the RNG).  The
    method lemmas below are therefore [Lemma]s -- several still [Admitted],
    which marks them as *in scope and unfinished* rather than assumed. *)

Require Export New.proof.go_etcd_io.raft.election_proof.defs.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** Two [own_map]s at the same location describe the same map.

    Not in [new/golang/theory/map.v], and provable there: [own_map] is
    [heap_pointsto mref dq mv] plus [is_map_pure mv mp] plus a pointwise
    agreement between [mp] and the [gmap], and [go.map_lookup_pure] says
    [map_lookup mv k = mp k] -- so [mp] is a function of [mv], and the
    points-to pins [mv].  Stated here at [w64 ↦ loc] because that is where
    it is needed; lift it into the framework when a second caller appears. *)
Lemma progress_map_agree (mref : loc) dq1 dq2 (m1 m2 : gmap w64 loc) :
  mref ↦${dq1} m1 -∗ mref ↦${dq2} m2 -∗ ⌜ m1 = m2 ⌝.
Proof using All.
  rewrite own_map_unseal /own_map_def.
  iIntros "H1 H2".
  iDestruct "H1" as (mv1 mp1) "(Hown1 & %Hmap1 & %Hag1 & _ & _)".
  iDestruct "H2" as (mv2 mp2) "(Hown2 & %Hmap2 & %Hag2 & _ & _)".
  iDestruct (heap_pointsto_agree with "[$Hown1 $Hown2]") as %->.
  iPureIntro. apply map_eq. intros k.
  pose proof (go.map_lookup_pure #k _ _ Hmap1) as He1.
  pose proof (go.map_lookup_pure #k _ _ Hmap2) as He2.
  specialize (Hag1 k). specialize (Hag2 k).
  assert (mp1 #k = mp2 #k) as Heq by congruence.
  rewrite Hag1 Hag2 in Heq.
  destruct (m1 !! k) as [v1|], (m2 !! k) as [v2|]; try congruence.
  injection Heq as Hv. by simplify_eq.
Qed.

(** The (fixed) set of voters. *)
Context (cfg : gset w64).

(** *** Inflights.

    A sliding window of in-flight append sizes.  Election never inspects it:
    [reset] allocates a fresh one per peer, and [maybeSendAppend] only asks
    whether it is full.  So the contents are existential -- what matters is
    that the object and its buffer are owned, so that a [Progress] can be
    overwritten wholesale. *)
(** [Full()]'s answer ([inflights_full], [defs.v]), read off the
    [Inflights] value ([Inflights__Fullⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3/tracker.v:201):

      in.count == in.size || (in.maxBytes != 0 && in.bytes >= in.maxBytes)

    [Inflights.Add] **panics** when it is [true] ("cannot add into a Full
    inflights", tracker.v:100), so [Add]'s triple can only be stated --
    truthfully -- at a window the caller knows is not full.  That is why
    [own_Inflights] is indexed by a record that determines it.  (Until
    2026-10-02 [inflights_full] was this right-hand side, on the Goose
    value.) *)
Lemma inflights_full_abs (iv : tracker.Inflights.t) :
  inflights_full (inflights_abs iv) =
  bool_decide (iv.(tracker.Inflights.count') = iv.(tracker.Inflights.size'))
  || (bool_decide (iv.(tracker.Inflights.maxBytes') ≠ W64 0) &&
      bool_decide (uint.Z iv.(tracker.Inflights.maxBytes')
                   ≤ uint.Z iv.(tracker.Inflights.bytes'))).
Proof.
  rewrite /inflights_full /inflights_abs /=. f_equal; [|f_equal].
  - apply bool_decide_ext. split; [intros; word | intros ->; done].
  - apply bool_decide_ext. split; intros H Hc; apply H; [rewrite Hc; done | word].
Qed.

(** The ring-buffer invariant, over the [Inflights] value and the *length* of
    the buffer it points at.

    [Add] writes [buffer[(start+count) mod size]] after growing the buffer on
    demand, so a triple for it is false without this: with, say,
    [start = 100], [count = 0], [size = 1000] and an empty buffer, [Add] is
    not [Full], grows the buffer to one slot and then indexes slot 100 --
    out of range.  The conjuncts, in order: [start] and [count] are
    non-negative, [count] fits the ring, the buffer is at most the ring, the
    ring is small enough that [len(buffer) * 2] in [grow] cannot overflow,
    [start] is a ring position (degenerately [0] when the ring is empty), and
    **every occupied slot is inside the buffer** -- either the occupied range
    does not wrap, or the buffer has already grown to the full ring.

    Note [0 ≤ buflen ≤ size] forces [0 ≤ size], so a degenerate
    [size = 0] ring is pinned to [start = count = buflen = 0]; that ring is
    always [Full], so [Add] is unreachable on it. *)
Definition inflights_ok (iv : tracker.Inflights.t) (buflen : Z) : Prop :=
  (0 ≤ sint.Z iv.(tracker.Inflights.start'))%Z ∧
  (0 ≤ sint.Z iv.(tracker.Inflights.count')
     ≤ sint.Z iv.(tracker.Inflights.size'))%Z ∧
  (0 ≤ buflen ≤ sint.Z iv.(tracker.Inflights.size'))%Z ∧
  (sint.Z iv.(tracker.Inflights.size') < 2 ^ 62)%Z ∧
  ((sint.Z iv.(tracker.Inflights.start') < sint.Z iv.(tracker.Inflights.size'))%Z
   ∨ (sint.Z iv.(tracker.Inflights.size') = 0
      ∧ sint.Z iv.(tracker.Inflights.start') = 0)%Z) ∧
  ((sint.Z iv.(tracker.Inflights.start') + sint.Z iv.(tracker.Inflights.count')
      ≤ buflen)%Z
   ∨ buflen = sint.Z iv.(tracker.Inflights.size')).

(** The **internal** predicate for an [Inflights] object, indexed by its
    value [iv] and the contents [buf] of its ring buffer.  [buf] is in the
    index because [grow] is specified by what it does to the buffer.  Only
    [Inflights]' own methods see it: [grow] is stated on it, and the other
    methods' proofs open [own_Inflights] to it.  (Until 2026-10-02 this was
    the one predicate, and every caller's spec named the Goose value; until
    2026-09-23 there were two forms, [own_inflights_at l iv] and the
    existential [own_inflights l]; notes/decisions.md, "Three layers".) *)
Definition own_inflights (l : loc) (iv : tracker.Inflights.t)
    (buf : list tracker.inflight.t) : iProp Σ :=
    "Hiv" ∷ l ↦ iv ∗
    "Hbuf" ∷ iv.(tracker.Inflights.buffer') ↦* buf ∗
    "Hbuf_cap" ∷ own_slice_cap tracker.inflight.t
                   iv.(tracker.Inflights.buffer') (DfracOwn 1) ∗
    "%Hinfl_ok" ∷ ⌜ inflights_ok iv (Z.of_nat (length buf)) ⌝.

(** The **public** predicate for an [Inflights] object, indexed by the
    record [inflights.t] ([defs.v]): how many messages and bytes are in
    flight, and the two limits -- exactly what the exported methods' specs
    ([Full], [Add], [FreeLE], [reset], [NewInflights]) say.  The ring
    buffer is hidden. *)
Definition own_Inflights (l : loc) (i : inflights.t) : iProp Σ :=
  ∃ (iv : tracker.Inflights.t) (buf : list tracker.inflight.t),
    "Hin" ∷ own_inflights l iv buf ∗
    "%Hiabs" ∷ ⌜ inflights_abs iv = i ⌝.

Lemma own_Inflights_intro l iv buf :
  own_inflights l iv buf -∗ own_Inflights l (inflights_abs iv).
Proof. iIntros "Hin". iExists iv, buf. by iFrame. Qed.

(** *** Per-peer replication progress.

    Ownership is of the whole [Progress] *value*, because [reset]'s [Visit]
    closure overwrites one wholesale
    ([pr <-[tracker.Progress] CompositeLiteral ...]); a predicate over
    selected fields could not justify that write.  What hangs off the value
    is its [Inflights] object.

    A field assignment like [becomeLeader]'s [pr.RecentActive := true] steps
    through [pr ↦ pv] with the generated [AccessStrict] instances and leaves
    [Inflights'] alone, so [own_inflights] survives it untouched. *)
(** The **public** predicate for a [Progress] object, indexed by the
    record [progress.t] ([defs.v]), which includes its [Inflights] window
    [infl].  [IsPaused]'s answer is a function of [state] and [paused], and
    [SentEntries] reaches [Inflights.Add], whose precondition is
    [inflights_full infl = false].

    [progress_abs pv infl = Some p] says what the two pure conjuncts of the
    old [own_progress pr pv iv] said (until 2026-10-02), and more:

    - **not a learner** ([IsLearner = false]): no learners are in scope.
      Added 2026-09-16 because [wp_raft__promotable] needs it: [promotable]
      returns [pr != nil && !pr.IsLearner && ...], and without it its
      postcondition [b = bool_decide (id ∈ cfg)] is not derivable.
    - **the state is one of the three** ([StateProbe]/[StateReplicate]/
      [StateSnapshot]): [Progress.IsPaused] **panics** on anything else
      ("unexpected state", tracker.v:456), and [bcastAppend] reaches it on
      every peer.  [reset]'s [Visit] closure writes a literal with no
      [State] field, i.e. the zero value [StateProbe], and [ResetState] is
      always passed one of the three.

    A field assignment like [becomeLeader]'s [pr.RecentActive := true]
    steps through ["Hpv"] with the generated [AccessStrict] instances and
    leaves [Inflights'] alone.  Ownership is of the whole [Progress]
    *value*, because [reset]'s [Visit] closure overwrites one wholesale. *)
Definition own_Progress (pr : loc) (p : progress.t) : iProp Σ :=
  ∃ (pv : tracker.Progress.t),
    "Hpv" ∷ pr ↦ pv ∗
    "Hinfl" ∷ own_Inflights pv.(tracker.Progress.Inflights') p.(progress.infl) ∗
    "%Habs" ∷ ⌜ progress_abs pv p.(progress.infl) = Some p ⌝.

(** Re-seal [own_Progress] after field writes: the record read off the
    value.  The pure premise is last, so that [iApply (own_Progress_intro
    with "Hpv Hinfl")] fixes the value from ["Hpv"] and leaves
    [progress_abs pv' (p.infl) = Some p] to [progress_abs_solve]. *)
Lemma own_Progress_intro pr (pv : tracker.Progress.t) (p : progress.t) :
  pr ↦ pv -∗ own_Inflights pv.(tracker.Progress.Inflights') p.(progress.infl) -∗
  ⌜ progress_abs pv p.(progress.infl) = Some p ⌝ -∗
  own_Progress pr p.
Proof. iIntros "Hpv Hinfl %Habs". iExists pv. iFrame "∗%". Qed.

(** The same, at the record read off the value: for a [Progress] written
    wholesale ([reset]'s [Visit] closure) or field by field, when the
    caller wants the record to be whatever the value says. *)
Definition progress_of (pv : tracker.Progress.t) (st : prstate.t) (i : inflights.t)
    : progress.t :=
  progress.mk pv.(tracker.Progress.Match') pv.(tracker.Progress.Next')
    pv.(tracker.Progress.sentCommit') st pv.(tracker.Progress.PendingSnapshot')
    pv.(tracker.Progress.RecentActive') pv.(tracker.Progress.MsgAppFlowPaused') i.

Lemma own_Progress_of pr (pv : tracker.Progress.t) (st : prstate.t) (i : inflights.t) :
  pv.(tracker.Progress.IsLearner') = false →
  pv.(tracker.Progress.State') = prstate_w64 st →
  pr ↦ pv -∗ own_Inflights pv.(tracker.Progress.Inflights') i -∗
  own_Progress pr (progress_of pv st i).
Proof.
  iIntros (Hl Hst) "Hpv Hinfl". iApply (own_Progress_intro _ _ (progress_of pv st i) with "Hpv Hinfl").
  iPureIntro. apply progress_abs_Some. rewrite /progress_of /=. split_and!; done.
Qed.

(** An id set ([map[uint64]struct{}]) that is either [nil] or owned.

    [own_tracker] used to say [Learners ↦$ learners] outright, and a map
    points-to implies a non-nil location ([own_map_not_nil],
    [new/golang/theory/map.v]).  But the tracker [newRaft] builds has
    [Learners = LearnersNext = nil]: [MakeProgressTracker] writes [nil]
    ([new/code/go_etcd_io/raft/v3/tracker.v], "only populated when used"),
    [Config.Clone] maps [nil] to [nil], and only adding a *learner* ever
    allocates one.  So until 2026-09-22 [own_tracker] -- and with it
    [own_raft_phys] -- was **unsatisfiable by any raft [newRaft] returns**.
    Found by writing [newRaft]'s spec; nothing on the election path reads
    either map, so the weakening costs no proof anything. *)
Definition own_idset_opt (m : loc) (ids : gmap w64 unit) : iProp Σ :=
  ⌜ m = map.nil ∧ ids = ∅ ⌝ ∨ m ↦$ ids.

(** *** The progress tracker.

    [trk] is embedded in the raft struct **by value**, so the tracker's own
    bytes are part of the [r ↦ rv] clause of [own_raft_phys] and must not be
    claimed a second time.  [own_tracker tv votes] therefore owns exactly
    what the tracker *value* [tv] points at: the vote map, the progress map
    together with the [Progress] objects in it, and the id sets of the
    configuration.  [votes] is the recorded vote tally.

    The configuration is *simple*, not joint -- no reconfiguration and no
    learners are in scope -- which is recorded the same way [readonly.v]
    records it: the [JointConfig] array is [[voters_ref; map.nil]].  The
    voter set and the domain of the progress map are both [cfg].

    It is indexed by one record [t : trk.t] ([defs.v]): the tally
    [t.votes], the progress map [t.prs], and [t.peers], what each
    [Progress] holds, by peer ([nstate.prvals]): [prs] and [peers] are
    paired key by key, so they have the same domain.  (Until 2026-10-02
    the three were separate arguments and [peers] held Goose values; until
    2026-09-29 the values were existential inside, and a caller that
    needed one across a call it made with the struct sealed had to take
    the tracker out of [own_raft_phys] on loan.) *)
Definition own_tracker (tv : tracker.ProgressTracker.t) (t : trk.t) : iProp Σ :=
  ∃ (voters_ref : loc) (voters : gmap w64 unit)
    (learners learnersNext : gmap w64 unit),
  "Hvotes" ∷ tv.(tracker.ProgressTracker.Votes') ↦$ t.(trk.votes) ∗
  (** **Read-only.**  The progress *map* is allocated once, by
      [newTracker]/[confchange], and on the election path nothing ever
      inserts into it or deletes from it -- only the [Progress] *values* it
      points at are written ([reset]'s [Visit] closure,
      [BecomeReplicate], [SentEntries]).  Holding it at [DfracDiscarded]
      records that, and buys the one thing an exclusive points-to cannot:
      the map is **duplicable**, so a proof can keep a copy of
      [⌜ prs !! to = Some pr ⌝] across a call that consumes and rebuilds the
      whole tracker.  [maybeSendAppend] needs exactly that -- it holds the
      raw [pr] pointer across [r.send(...)], which is specified on
      [own_raft_phys] and so takes the tracker with it, and must then call
      [pr.SentEntries]/[pr.SentCommit] on the *same* pointer.  With an
      existentially quantified exclusive map there is no way back to that
      pointer; see [own_tracker_lookup] below.  Changed 2026-09-20.

      It is a genuine restriction: a proof of a reconfiguration path would
      have to take the map back to [DfracOwn 1].  Reconfiguration is out of
      scope (see [HnoConfChange] in [inv_raftlog.v]). *)
  "#Hprs" ∷ tv.(tracker.ProgressTracker.Progress') ↦$□ t.(trk.prs) ∗
  "Hprogs" ∷ ([∗ map] pr; p ∈ t.(trk.prs); t.(trk.peers), own_Progress pr p) ∗
  "%Hprs_dom" ∷ ⌜ dom t.(trk.prs) = cfg ⌝ ∗
  (* a simple configuration: second component of the joint config is nil *)
  "%Hvoters_arr" ∷ ⌜ array.arr
      tv.(tracker.ProgressTracker.Config').(tracker.Config.Voters')
      = [voters_ref; map.nil] ⌝ ∗
  (* and not a joint one on its way out: [AutoLeave] is only set on
     entering a joint configuration.  [ConfState] reads it (added
     2026-09-29, when [switchToConfig] stopped keeping the tracker value
     in hand across the call) *)
  "%Hautoleave" ∷ ⌜ tv.(tracker.ProgressTracker.Config').(tracker.Config.AutoLeave') = false ⌝ ∗
  "Hvoters" ∷ voters_ref ↦$ voters ∗
  "%Hvoters_dom" ∷ ⌜ dom voters = cfg ⌝ ∗
  (* no learners.  Either map may be [nil] -- and after [newRaft] both
     are: see [own_idset_opt]. *)
  "Hlearners" ∷ own_idset_opt
                  tv.(tracker.ProgressTracker.Config').(tracker.Config.Learners')
                  learners ∗
  "HlearnersNext" ∷ own_idset_opt
      tv.(tracker.ProgressTracker.Config').(tracker.Config.LearnersNext')
      learnersNext ∗
  "%Hno_learners" ∷ ⌜ learners = ∅ ∧ learnersNext = ∅ ⌝ ∗
  (* [campaign] does [make([]uint64, 0, len(idMap))], and [wp_slice_make3]
     needs [0 ≤ sint.Z cap].  Nothing else bounds the voter set: no Iris
     ownership constrains the cardinality of a [gset w64], so [size cfg =
     2^64] is consistent with every other conjunct here.  This is a property
     of the configuration, so it belongs with the configuration. *)
  "%Hcfg_size" ∷ ⌜ Z.of_nat (size cfg) < 2 ^ 63 ⌝ ∗
  (* **No non-emptiness conjunct.**  From 2026-09-16 to 2026-09-29 this
     predicate required [cfg ≠ ∅], because [MajorityConfig.VoteResult]
     returns [VoteWon] outright for an empty configuration while
     [is_quorum ∅ q] is false.  That made the *empty* tracker
     [MakeProgressTracker] builds -- the one [newRaft] starts from -- not an
     [own_tracker], so [newRaft] had to hold it on loan until
     [switchToConfig].  The premise now sits where it is used:
     [JointConfig.VoteResult], [TallyVotes] and [poll] take [cfg ≠ ∅]. *)
  (** **The inflight window is a sane size.**  [Config.validate] requires
      only [MaxInflightMsgs > 0] -- **it has no upper bound** (this comment
      said [(0, 1<<30]] until 2026-09-24; notes/false-statements.md) --
      and [newRaft] copies it into the tracker, so the [< 2^62] half is an
      extra premise of [newRaft]'s spec, not something raft checks.  So
      this predicate excludes valid configs with [MaxInflightMsgs ≥ 2^62].
      Needed because [reset]'s [Visit] closure calls
      [tracker.NewInflights(r.trk.MaxInflight, …)], and the ring-buffer
      invariant of [own_inflights] pins [0 ≤ size < 2^62] (see
      [inflights_ok]).  Like [Hcfg_size] it is a property of
      the configuration and is never written on the election path.
      Added 2026-09-20 for [bcastAppend]. *)
  "%HmaxInfl" ∷ ⌜ (0 ≤ sint.Z tv.(tracker.ProgressTracker.MaxInflight')
                     < 2 ^ 62)%Z ⌝.


(** *** Pure facts about the quorum vocabulary

    [TallyVotes] has to connect what the Go code counts to what the model
    says.  These lemmas are the bridge, and they are pure Rocq -- no program,
    no ownership -- so they are stated here rather than inside a proof.
    [is_quorum], [granted] and [rejected] are from
    [election_proof/protocol.v]. *)

Lemma elem_of_granted (votes : gmap w64 bool) k :
  k ∈ granted votes ↔ votes !! k = Some true.
Proof.
  rewrite /granted elem_of_dom. split.
  - intros [v Hv]. apply map_lookup_filter_Some in Hv as [Hv Hp].
    simpl in Hp. by subst.
  - intros Hv. exists true. by apply map_lookup_filter_Some_2.
Qed.

Lemma elem_of_rejected (votes : gmap w64 bool) k :
  k ∈ rejected votes ↔ votes !! k = Some false.
Proof.
  rewrite /rejected elem_of_dom. split.
  - intros [v Hv]. apply map_lookup_filter_Some in Hv as [Hv Hp].
    simpl in Hp. by subst.
  - intros Hv. exists false. by apply map_lookup_filter_Some_2.
Qed.

(** Go computes the majority threshold as [q := len(c)/2 + 1] and tests
    [votedCnt >= q]; the model says [size cfg < 2 * size (q ∩ cfg)].  They
    agree, integer division and all. *)
Lemma is_quorum_alt (q : gset w64) :
  is_quorum cfg q ↔ (size cfg / 2 + 1 ≤ size (q ∩ cfg))%nat.
Proof.
  rewrite /is_quorum.
  pose proof (Nat.div_mod_eq (size cfg) 2).
  pose proof (Nat.mod_upper_bound (size cfg) 2 ltac:(lia)).
  lia.
Qed.

(** A voter that has not rejected has either granted or not answered, which
    is why [MajorityConfig.VoteResult]'s [votedCnt + missing] is exactly
    [size (cfg ∖ rejected votes)] -- the quantity [step_lose] talks about. *)
Lemma cfg_minus_rejected (votes : gmap w64 bool) :
  cfg ∖ rejected votes = (granted votes ∩ cfg) ∪ (cfg ∖ dom votes).
Proof.
  apply set_eq. intros k.
  rewrite elem_of_union elem_of_intersection !elem_of_difference
          elem_of_granted elem_of_rejected elem_of_dom.
  destruct (votes !! k) as [[]|] eqn:Hk; naive_solver.
Qed.

Lemma granted_missing_disjoint (votes : gmap w64 bool) :
  (granted votes ∩ cfg) ## (cfg ∖ dom votes).
Proof.
  apply elem_of_disjoint. intros k Hk1 Hk2.
  rewrite elem_of_intersection elem_of_granted in Hk1.
  rewrite elem_of_difference elem_of_dom in Hk2.
  naive_solver.
Qed.

Lemma size_cfg_minus_rejected (votes : gmap w64 bool) :
  size (cfg ∖ rejected votes)
  = (size (granted votes ∩ cfg) + size (cfg ∖ dom votes))%nat.
Proof.
  rewrite cfg_minus_rejected size_union //. apply granted_missing_disjoint.
Qed.

(** *** Counting along a map enumeration

    [wp_map_for_range] ([new/golang/theory/map.v]) hands the proof an
    arbitrary duplicate-free enumeration [keys] of the map's domain and an
    index [i] into it, so a loop that counts has to count over a *list*.
    [nsat] is that count; [nsat_size] converts it back to a set cardinality
    once the range is over. *)
Definition nsat (P : w64 → Prop) `{∀ k, Decision (P k)} (l : list w64) : nat :=
  length (filter P l).

Lemma nsat_snoc (P : w64 → Prop) `{∀ k, Decision (P k)} l k :
  nsat P (l ++ [k]) = (nsat P l + if decide (P k) then 1 else 0)%nat.
Proof.
  rewrite /nsat filter_snoc length_app.
  destruct (decide (P k)); simpl; lia.
Qed.

Lemma nsat_le (P : w64 → Prop) `{∀ k, Decision (P k)} l :
  (nsat P l ≤ length l)%nat.
Proof. rewrite /nsat. apply length_filter. Qed.

Lemma nsat_size (Y : gset w64) (keys : list w64)
  (P : w64 → Prop) `{∀ k, Decision (P k)} :
  (∀ k, k ∈ cfg → (k ∈ Y ↔ P k)) →
  Y ⊆ cfg →
  NoDup keys →
  (list_to_set keys : gset w64) = cfg →
  nsat P keys = size Y.
Proof.
  intros HY Hsub Hnd Hset.
  rewrite /nsat -(size_list_to_set (C:=gset w64) (filter P keys));
    last by apply list.NoDup_filter.
  f_equal. apply set_eq. intros k.
  rewrite elem_of_list_to_set list_elem_of_filter. split.
  - intros [HP Hk].
    assert (k ∈ cfg) as Hkc by (rewrite -Hset elem_of_list_to_set //).
    by apply (HY k Hkc).
  - intros HkY.
    assert (k ∈ cfg) as Hkc by (by apply Hsub).
    split; first by apply (HY k Hkc).
    rewrite -(elem_of_list_to_set (C:=gset w64)) Hset //.
Qed.

Lemma nsat_granted (votes : gmap w64 bool) (keys : list w64) :
  NoDup keys → (list_to_set keys : gset w64) = cfg →
  nsat (λ k, votes !! k = Some true) keys = size (granted votes ∩ cfg).
Proof.
  intros Hnd Hset. apply nsat_size; [|set_solver|done|done].
  intros k Hk. rewrite elem_of_intersection elem_of_granted. naive_solver.
Qed.

Lemma nsat_rejected (votes : gmap w64 bool) (keys : list w64) :
  NoDup keys → (list_to_set keys : gset w64) = cfg →
  nsat (λ k, votes !! k = Some false) keys = size (rejected votes ∩ cfg).
Proof.
  intros Hnd Hset. apply nsat_size; [|set_solver|done|done].
  intros k Hk. rewrite elem_of_intersection elem_of_rejected. naive_solver.
Qed.

Lemma nsat_missing (votes : gmap w64 bool) (keys : list w64) :
  NoDup keys → (list_to_set keys : gset w64) = cfg →
  nsat (λ k, votes !! k = None) keys = size (cfg ∖ dom votes).
Proof.
  intros Hnd Hset. apply nsat_size; [|set_solver|done|done].
  intros k Hk. rewrite elem_of_difference elem_of_dom.
  destruct (votes !! k) eqn:Hv; naive_solver.
Qed.

(** [len] of a *named* map type.

    [new/golang/defn/map.v] declares its [FuncUnfold] instances at
    [go.MapType key_type elem_type] literally, unlike [slice.v:133] which
    takes any [st ↓u go.SliceType elem_type].  So [wp_auto] cannot step
    [len(p.Progress)], whose static type is the named [tracker.ProgressMap]
    -- and the symptom is a bare
    [#(sem.(go.sem_fn).(functions) go.len [tracker.ProgressMap])] that no
    tactic touches.  [go.len_underlying] ([new/golang/defn/predeclared.v:553])
    is the way through; it is the only [FuncUnfold]-for-a-named-type escape
    hatch the predeclared semantics offers.

    Used by [Visit] once that is unblocked (see below); kept here because
    working this out is the sort of thing one should not have to do twice. *)
Lemma wp_ProgressMap_len (mref : loc) dq (m : gmap w64 loc) :
  {{{ mref ↦${dq} m }}}
    #(functions go.len [tracker.ProgressMap]) #mref
  {{{ RET #(W64 (size m)); mref ↦${dq} m }}}.
Proof.
  wp_start_folded as "Hm".
  rewrite (go.len_underlying tracker.ProgressMap).
  rewrite (go.is_underlying (t := tracker.ProgressMap)
             (tunder := go.MapType go.uint64 (go.PointerType tracker.Progress))).
  wp_apply (wp_map_len with "Hm") as "Hm".
  iApply "HΦ". iFrame.
Qed.


(** [trk.Visit f] calls [f id pr] on every voter's [Progress].

    The closure is handed full ownership of one [Progress], the tracker field
    [trk ↦ tv], a wand that turns that [Progress] back into the **whole**
    tracker, and whatever the caller lends it ([I]).  It gives back the
    tracker (not the lone [Progress]), the field and [I].  [reset]'s closure
    needs the first three: it overwrites the [Progress], reads
    [r.trk.MaxInflight] and [r.trk.MaxInflightBytes] through the field, and
    reads [r.raftLog] and [r.id] through [I]; it applies the wand at the end.

    **Why the wand, and why the tracker comes back whole** (changed
    2026-09-20 for [bcastAppend]).  [bcastAppend]'s closure calls
    [r.sendAppend(id)], which reaches [maybeSendAppend]; that function looks
    the peer up in [r.trk.Progress] *itself* and then calls [r.send], whose
    triple is stated on [own_raft_phys] -- which contains [own_tracker].  So
    the closure needs the entire tracker, not one [Progress] out of it, and
    with only [own_Progress pr] in hand it could not even step the
    [map.lookup1].  Handing it [own_Progress pr] *plus* the accessor wand
    costs [Visit] nothing (it does its own lookup before each call and does
    not touch the map during one) and leaves [reset]'s closure free to keep
    using the lone [Progress].  The postcondition asks only for the tracker
    back because a closure that has already merged the [Progress] into it --
    as [bcastAppend]'s must -- cannot split the same one out again: nothing
    in [own_tracker] says which key [pr] sits at.

    The [i ∈ cfg] premise is likewise for [bcastAppend]: its closure calls
    [r.sendAppend(id)], and [maybeSendAppend] looks [id] up in the progress
    map itself, which only hits for a voter.  [Visit] has it -- it only
    enumerates keys of [prs], whose domain is [cfg].

    **Why the tracker value may change** ([tv] is quantified per call, and
    the closure gives back some [tv'], possibly different).  This is not
    generality for its own sake; without it [bcastAppend] is not provable.
    Its closure has to run [r.sendAppend(id)], whose triple -- like every
    triple below [raft.send] -- is stated on [own_raft_phys], which packages
    the *whole* struct as [∃ rv, r ↦ rv ∗ …].  So the closure must merge the
    lent [trk ↦ tv] back into [r ↦ rv] before the call, and what comes back
    is a fresh, existentially quantified [rv'].  Nothing in [own_raft_phys]
    ties [rv'.(trk')] to [tv] -- [send] does not touch the field, but its
    *spec* cannot say so -- so a closure obliged to return the field at the
    original [tv] would be stuck.  Returning it at whatever value the
    rebuilt struct has costs [Visit] nothing: it re-reads [p.Progress]
    through the field on every iteration anyway, and all it needs of the
    tracker is [dom prs = cfg], which [own_tracker] gives at any [tv'].
    [reset]'s closure simply returns the [tv] it was handed.

    The [MaxInflight] bound comes along for the same reason.  [reset]'s
    closure calls [NewInflights(r.trk.MaxInflight, …)], whose premise it is
    ([inflights_ok], above); with the tracker value quantified per call the
    closure can no longer read that bound out of the enclosing proof's
    context, and it cannot read it out of [own_tracker] either -- it holds
    the tracker only as a wand, and cashing that wand costs it the
    [own_Progress] it is there to overwrite.  So [Visit], which does hold
    the tracker, hands the fact over.

    **Why the progress map stays fixed** ([prs]).  The tracker value may
    change, but the progress map may not: nothing on the election path
    inserts into or deletes from it, and [own_tracker] is indexed by it
    (2026-09-23), so the closure hands the tracker back at the same [prs]
    and [Visit] promises the same of itself.  That is what lets [reset] --
    which runs [Visit] -- re-establish [own_raft_phys], whose tracker is at
    [nstate.progress].

    **Why the field is lent rather than kept.**  [Visit] itself reads
    [p.Progress] on every iteration, so it cannot hand the field over for
    good; and the closure reads a *different* sub-field of the same value,
    so it cannot be denied it.  The two reads are at different times, so
    lending resolves it.  See [spec_ProgressTracker__Visit.v] for how this
    was got wrong. *)
(** **The caller invariant is indexed** (2026-10-01) by the set [D] of ids
    visited so far and the tracker's current [Progress] values: the closure
    takes [I D pvs] to [I ({[i]} ∪ D) pvs'].  [reset] needs both -- its
    postcondition says what [Match] every voter ends with, which is a fact
    about every key, and about the values the tracker holds -- and [Visit]
    ends at [I cfg]. *)
Definition visit_closure (trk : loc) (votes : gmap w64 bool)
  (prs : gmap w64 loc) (f : func.t)
  (I : gset w64 → gmap w64 progress.t → iProp Σ)
  : iProp Σ :=
  ∀ (i : w64) (pr : loc) (tv : tracker.ProgressTracker.t)
    (pvs : gmap w64 progress.t) (p : progress.t) (D : gset w64),
    {{{ ⌜ i ∈ cfg ⌝ ∗ ⌜ prs !! i = Some pr ⌝ ∗ ⌜ pvs !! i = Some p ⌝ ∗
        ⌜ (0 ≤ sint.Z tv.(tracker.ProgressTracker.MaxInflight') < 2 ^ 62)%Z ⌝ ∗
        trk ↦ tv ∗ own_Progress pr p ∗
        (∀ p', own_Progress pr p' -∗
               own_tracker tv (trk.mk votes prs (<[i := p']> pvs))) ∗ I D pvs }}}
      #f #i #pr
    {{{ RET #(); ∃ tv' pvs', trk ↦ tv' ∗ own_tracker tv' (trk.mk votes prs pvs') ∗
                             I ({[i]} ∪ D) pvs' }}}.


(** The inflight-window bound, read out without consuming the tracker.
    [reset]'s [Visit] closure calls [tracker.NewInflights(r.trk.MaxInflight,
    ...)], whose premise this is; the closure cannot reach [own_tracker]
    itself, so [reset] pulls the fact into the Coq context before the
    [Visit]. *)
Lemma own_tracker_maxinflight tv t :
  own_tracker tv t -∗
  ⌜ (0 ≤ sint.Z tv.(tracker.ProgressTracker.MaxInflight') < 2 ^ 62)%Z ⌝ ∗
  own_tracker tv t.
Proof using All.
  iIntros "Hown". iNamed "Hown".
  iSplitR; first (iPureIntro; exact HmaxInfl).
  rewrite /own_tracker. iExists voters_ref, voters, learners, learnersNext.
  iFrame "∗#%".
Qed.

(** Borrow one voter's [Progress] out of the tracker, by its key in the
    progress map the tracker is indexed by, at the record [t.peers] holds
    for it; give it back at any record, which the index then records.  The
    caller can come back to the *same* pointer, and the same record, after
    any call that returns the tracker at the same [prs] and [peers]. *)
Lemma own_tracker_lookup tv (t : trk.t) (i : w64) (pr : loc) :
  t.(trk.prs) !! i = Some pr →
  own_tracker tv t -∗
  ∃ p, ⌜ t.(trk.peers) !! i = Some p ⌝ ∗ own_Progress pr p ∗
    (∀ p', own_Progress pr p' -∗
           own_tracker tv (trk.mk t.(trk.votes) t.(trk.prs) (<[i := p']> t.(trk.peers)))).
Proof using All.
  intros Hpr. iIntros "Hown". iNamed "Hown".
  iDestruct (big_sepM2_lookup_iff with "Hprogs") as %Hiff.
  destruct (Hiff i) as [Hsome _]. destruct (Hsome ltac:(by eexists)) as [p Hv].
  iDestruct (big_sepM2_insert_acc _ _ _ _ _ _ Hpr Hv with "Hprogs") as "[Hp Hback]".
  iExists p. iSplitR; first done. iFrame "Hp".
  iIntros (p') "Hp".
  iDestruct ("Hback" $! pr p' with "Hp") as "Hprogs".
  rewrite (insert_id t.(trk.prs) i pr) //.
  rewrite /own_tracker.
  iExists voters_ref, voters, learners, learnersNext.
  iFrame "∗#%".
Qed.

(** The same, given back at the record it was borrowed at. *)
Lemma own_tracker_lookup_same tv (t : trk.t) (i : w64) (pr : loc) :
  t.(trk.prs) !! i = Some pr →
  own_tracker tv t -∗
  ∃ p, ⌜ t.(trk.peers) !! i = Some p ⌝ ∗ own_Progress pr p ∗
    (own_Progress pr p -∗ own_tracker tv t).
Proof using All.
  intros Hpr. iIntros "Hown".
  iDestruct (own_tracker_lookup _ _ _ _ Hpr with "Hown")
    as (p Hv) "[Hp Hback]".
  iExists p. iSplitR; first done. iFrame "Hp".
  iIntros "Hp". iDestruct ("Hback" with "Hp") as "Hown".
  rewrite (insert_id t.(trk.peers) i p) //.
Qed.

(** The [Progress] records are indexed by the same peers as the map. *)
Lemma own_tracker_prvals_dom tv t :
  own_tracker tv t -∗
  ⌜ dom t.(trk.peers) = dom t.(trk.prs) ⌝ ∗ own_tracker tv t.
Proof using All.
  iIntros "Hown". iNamed "Hown".
  iDestruct (big_sepM2_dom with "Hprogs") as %Hd.
  iSplitR; first done.
  rewrite /own_tracker. iExists voters_ref, voters, learners, learnersNext.
  iFrame "∗#%".
Qed.

(** Read the progress map's points-to and domain out of the tracker without
    consuming it (the map is read-only, hence persistent). *)
Lemma own_tracker_progress_map tv t :
  own_tracker tv t -∗
  tv.(tracker.ProgressTracker.Progress') ↦$□ t.(trk.prs) ∗ ⌜ dom t.(trk.prs) = cfg ⌝ ∗
  own_tracker tv t.
Proof using All.
  iIntros "Hown". iNamed "Hown".
  iFrame "Hprs". iSplitR; first (iPureIntro; exact Hprs_dom).
  rewrite /own_tracker. iExists voters_ref, voters, learners, learnersNext.
  iFrame "∗#%".
Qed.

(** [trk.Progress[i]], for a voter [i]: [becomeLeader] looks up [r.id].
    Only voters are in the map, whence the side condition.  The [Progress]
    comes out as [own_tracker_lookup] hands it out. *)
Lemma wp_tracker_progress_lookup tv t (i : w64) :
  i ∈ cfg →
  {{{ own_tracker tv t }}}
    map.lookup1 go.uint64 (go.PointerType tracker.Progress)
      #(tv.(tracker.ProgressTracker.Progress')) #i
  {{{ (pr : loc), RET #pr;
      ⌜ t.(trk.prs) !! i = Some pr ⌝ ∗
      ∃ p, ⌜ t.(trk.peers) !! i = Some p ⌝ ∗ own_Progress pr p ∗
        (∀ p', own_Progress pr p' -∗
               own_tracker tv (trk.mk t.(trk.votes) t.(trk.prs) (<[i := p']> t.(trk.peers)))) }}}.
Proof.
  intros Hi. iIntros (Φ) "Hown HΦ".
  iDestruct (own_tracker_progress_map with "Hown") as "(#Hprs & %Hdom & Hown)".
  assert (is_Some (t.(trk.prs) !! i)) as [pr Hpr].
  { apply elem_of_dom. rewrite Hdom //. }
  wp_apply (wp_map_lookup1 with "Hprs") as "_".
  rewrite Hpr /=.
  iApply ("HΦ" $! pr). iSplitR; first done.
  iApply (own_tracker_lookup _ _ _ _ Hpr with "Hown").
Qed.


End proof.

(** Open [own_Progress]: after [iNamed "Hpr"], turn ["%Habs"] into the
    record's fields, written as the value's -- [p] becomes
    [progress.mk pv.Match' pv.Next' … st … inf], with [Hst] relating [st] to
    [pv.State'] and [Hl] saying [pv] is not a learner's. *)
Ltac progress_open Habs p :=
  let Hl := fresh "Hl" in let Hst := fresh "Hst" in
  apply progress_abs_Some in Habs as (Hl & Hst & ? & ? & ? & ? & ? & ? & _);
  let m := fresh "m" in let n := fresh "n" in let sc := fresh "sc" in
  let st := fresh "st" in let ps := fresh "ps" in let ra := fresh "ra" in
  let pa := fresh "pa" in let inf := fresh "inf" in
  destruct p as [m n sc st ps ra pa inf];
  cbn [progress.matched progress.next progress.sent_commit progress.state
       progress.pending_snapshot progress.recent_active progress.paused
       progress.infl] in *;
  subst m n sc ps ra pa.

(** The pure side of [own_Progress_intro]: every field of the value against
    the record. *)
Ltac progress_abs_solve :=
  apply progress_abs_Some; simpl; split_and?; try done.

(** Reduce the tracker record's projections everywhere, after
    [destruct t as [votes prs pvs]] and [iNamed] of [own_tracker]. *)
Ltac trk_simpl := cbn [trk.votes trk.prs trk.peers] in *.

(** Reduce the record's projections, and nothing else (safe on a [WP]
    goal). *)
Ltac progress_simpl :=
  cbn [progress.matched progress.next progress.sent_commit progress.state
       progress.pending_snapshot progress.recent_active progress.paused
       progress.infl].

(** The pure side of [own_Progress_intro] after a run of field writes, from
    the [progress_abs] fact the predicate was opened with: unfold the
    record methods, reduce, and match field by field.  For a goal that is
    pure (after [iPureIntro]) -- it runs [simpl in *]. *)
Ltac progress_abs_from Habs :=
  apply progress_abs_Some in Habs; apply progress_abs_Some;
  try unfold progress_reset_state, progress_become_probe, progress_become_probe_next,
             progress_become_replicate, progress_become_snapshot,
             progress_sent_entries, progress_sent_commit, progress_maybe_update,
             progress_maybe_decr_to in *;
  unfold w64_max, w64_min in *;
  simpl in *;
  repeat match goal with H : _ ∧ _ |- _ => destruct H end;
  repeat match goal with
         | H : ?f ?x = _ |- _ => is_var x; progress (rewrite H); clear H
         end;
  split_and?; try done; try congruence.

(** ** A configuration, and changing to one

    [own_config cfg cfgv prsm prs] is what [confchange.Restore] builds for a
    voters-only configuration [cfg]: the [Config] value [cfgv] with its
    voter map, and the progress map at [prsm] with its [Progress] objects.
    It is the part of [own_tracker] that [switchToConfig] replaces; the
    vote tally and the tracker's other fields stay.  [own_tracker_reconfig]
    is the one place an [own_tracker] changes its [cfg] index. *)
Section config.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Definition own_config (cfg : gset w64) (cfgv : tracker.Config.t) (prsm : loc)
    (prs : gmap w64 loc) : iProp Σ :=
  ∃ (vref : loc) (vm : gmap w64 unit),
  "%Hcfgarr" ∷ ⌜ array.arr cfgv.(tracker.Config.Voters') = [vref; map.nil] ⌝ ∗
  "%Hcfgl" ∷ ⌜ cfgv.(tracker.Config.Learners') = map.nil ⌝ ∗
  "%Hcfgln" ∷ ⌜ cfgv.(tracker.Config.LearnersNext') = map.nil ⌝ ∗
  "%Hcfgal" ∷ ⌜ cfgv.(tracker.Config.AutoLeave') = false ⌝ ∗
  "Hvref" ∷ vref ↦$ vm ∗
  "%Hvm" ∷ ⌜ dom vm = cfg ⌝ ∗
  "#Hprsm" ∷ prsm ↦$□ prs ∗
  "%Hprs" ∷ ⌜ dom prs = cfg ⌝ ∗
  "Hprogs" ∷ ([∗ map] pr ∈ prs, ∃ p, own_Progress pr p) ∗
  "%Hcsz" ∷ ⌜ Z.of_nat (size cfg) < 2 ^ 63 ⌝.

(** Name the values of a map's worth of objects: a [big_sepM] of
    existentials is a [big_sepM2] against some map of witnesses. *)
Lemma big_sepM_exist_sepM2 {A B : Type} (m : gmap w64 A) (Φ : w64 → A → B → iProp Σ) :
  ([∗ map] k ↦ x ∈ m, ∃ y, Φ k x y) -∗
  ∃ m' : gmap w64 B, [∗ map] k ↦ x; y ∈ m; m', Φ k x y.
Proof.
  induction m as [|k x m Hk IH] using map_ind.
  - iIntros "_". iExists ∅. by rewrite big_sepM2_empty.
  - rewrite big_sepM_insert //. iIntros "[[%y Hy] Hm]".
    iDestruct (IH with "Hm") as (m') "Hm".
    iExists (<[k := y]> m').
    iApply (big_sepM2_insert_2 with "Hy Hm").
Qed.

(** The tracker [MakeProgressTracker] builds is an [own_tracker] over the
    empty configuration. *)
Lemma own_tracker_empty (tv : tracker.ProgressTracker.t) (v0 : loc) :
  array.arr tv.(tracker.ProgressTracker.Config').(tracker.Config.Voters') = [v0; map.nil] →
  tv.(tracker.ProgressTracker.Config').(tracker.Config.Learners') = map.nil →
  tv.(tracker.ProgressTracker.Config').(tracker.Config.LearnersNext') = map.nil →
  tv.(tracker.ProgressTracker.Config').(tracker.Config.AutoLeave') = false →
  (0 ≤ sint.Z tv.(tracker.ProgressTracker.MaxInflight') < 2 ^ 62)%Z →
  v0 ↦$ (∅ : gmap w64 unit) -∗
  tv.(tracker.ProgressTracker.Votes') ↦$ (∅ : gmap w64 bool) -∗
  tv.(tracker.ProgressTracker.Progress') ↦$□ (∅ : gmap w64 loc) -∗
  own_tracker ∅ tv (trk.mk ∅ ∅ ∅).
Proof using All.
  iIntros (Harr Hl Hln Hal Hmi) "Hv0 Hvotes #Hprs".
  rewrite /own_tracker. iExists v0, ∅, ∅, ∅.
  iFrame "Hvotes Hprs Hv0". rewrite Hl Hln.
  iSplitL; first by rewrite big_sepM2_empty.
  repeat (iSplitR; [first [iPureIntro; done | iLeft; done] |]).
  iPureIntro. split_and!; try done; rewrite ?dom_empty_L ?size_empty //; lia.
Qed.

(** Replace the configuration and the progress map of a tracker, keeping
    its tally and inflight bound.  The old configuration's voter map and
    [Progress] objects are dropped; the new ones hold whatever [Restore]
    put in them. *)
Lemma own_tracker_reconfig cfg0 cfg tv t cfgv prsm prs :
  own_tracker cfg0 tv t -∗
  own_config cfg cfgv prsm prs -∗
  ∃ pvs, own_tracker cfg (tv <| tracker.ProgressTracker.Config' := cfgv |>
                             <| tracker.ProgressTracker.Progress' := prsm |>)
                     (trk.mk t.(trk.votes) prs pvs).
Proof using All.
  iIntros "Hold Hnew". iNamed "Hold".
  iClear "Hprs Hprogs Hvoters Hlearners HlearnersNext".
  iNamed "Hnew".
  iDestruct (big_sepM_exist_sepM2 (B:=progress.t) _ (λ _ pr p, own_Progress pr p)
               with "Hprogs") as (pvs) "Hprogs".
  iExists pvs.
  rewrite /own_tracker. iExists vref, vm, ∅, ∅. simpl.
  iFrame "Hvotes Hprsm Hprogs Hvref". rewrite Hcfgl Hcfgln.
  repeat (iSplitR; [first [iPureIntro; done | iLeft; done] |]).
  iPureIntro. done.
Qed.

End config.

(* ===================================================================== *)
(** ** Replication-side additions (2026-10-01)

    Added for the log-replication tracker collections
    ([Progress.MaybeUpdate]/[MaybeDecrTo]/[BecomeProbe]/[CanBumpCommit],
    [Inflights.FreeLE], [ProgressTracker.Committed] and the quorum
    functions under it).  Kept at the end of the file, apart from the
    election-era definitions above, so that concurrent edits merge. *)


Set Default Proof Using "Type".

(* [w64_min]/[w64_max] moved to [defs.v] (2026-10-02), with the
   [Progress] methods that use them. *)

(** Each voter's [Match], read off the tracker's [Progress] values, with
    [0] for a peer that has none (there is none such in [cfg]:
    [own_tracker]'s two maps have domain [cfg]).  [pvs_acked] is the
    [Option] form, which is what [matchAckIndexer.AckedIndex] returns. *)
Definition pvs_acked (pvs : gmap w64 progress.t) (v : w64) : option w64 :=
  progress.matched <$> pvs !! v.
Definition pvs_match_at (pvs : gmap w64 progress.t) (v : w64) : w64 :=
  default (W64 0) (pvs_acked pvs v).

(** [N] is the quorum index of the per-voter values [f] over the voter set
    [s] -- what [MajorityConfig.CommittedIndex] computes by sorting:
    [N] is one of the values, a quorum of [s] has a value [≥ N], and no
    larger index has a quorum.  [is_quorum] is [protocol.v]'s. *)
Definition is_quorum_index (s : gset w64) (f : w64 → w64) (N : w64) : Prop :=
  (∃ v, v ∈ s ∧ f v = N) ∧
  is_quorum s (filter (λ v, uint.Z N ≤ uint.Z (f v)) s) ∧
  (∀ N' : w64, uint.Z N < uint.Z N' →
         ¬ is_quorum s (filter (λ v, uint.Z N' ≤ uint.Z (f v)) s)).

Section replication.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** [min] on [uint64]; the framework has [wp_max2_uint64] but no [min]. *)
Lemma wp_min2_uint64 (x y : w64) :
  {{{ True }}}
    #(functions go.min [go.uint64; go.uint64]) #x #y
  {{{ RET #(w64_min x y); True }}}.
Proof.
  change ([ _ ;  _]) with (replicate 2 go.uint64).
  wp_start. rewrite /w64_min. wp_if_destruct; wp_end; destruct decide; try done; word.
Qed.

(** The progress *map* with the [Progress] objects it points at -- the
    object a [tracker.matchAckIndexer] is (a named [ProgressMap]), and
    exactly [own_tracker]'s ["Hprs"] and ["Hprogs"] conjuncts.  It is the
    precondition of [matchAckIndexer.AckedIndex], which receives the map and
    not the tracker: [ProgressTracker.Committed] hands
    [matchAckIndexer(p.Progress)] to [JointConfig.CommittedIndex], which
    reads the voter map out of the *same* tracker while the indexer is in
    use, so the indexer cannot be specified on [own_tracker] whole. *)
Definition own_progress_map (m : loc) (prs : gmap w64 loc)
    (pvs : gmap w64 progress.t) : iProp Σ :=
  "#Hprs" ∷ m ↦$□ prs ∗
  "Hprogs" ∷ ([∗ map] pr; p ∈ prs; pvs, own_Progress pr p).

(** The [quorum.AckedIndexer] interface contract, against a resource [P]
    the implementation needs and a function [acked] saying what each id's
    acknowledged index is ([None]: "not a voter I know", which
    [MajorityConfig.CommittedIndex] counts as [0]).  Persistent, like
    [is_Storage] ([inv_storage.v]); one triple per method. *)
Definition is_AckedIndexer (l : interface.t) (P : iProp Σ)
    (acked : w64 → option w64) : iProp Σ :=
  ∃ (i : interface.t_ok),
  "%Hlok" ∷ ⌜ l = interface.ok i ⌝ ∗
  "#HAckedIndex" ∷ □ (∀ (id : w64),
     {{{ P }}}
       #(methods i.(interface.ty) "AckedIndex"%go i.(interface.v)) #id
     {{{ RET (#(default (W64 0) (acked id)), #(bool_decide (is_Some (acked id)))); P }}}).

End replication.
