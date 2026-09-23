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
(** [Full()]'s answer, read off the [Inflights] value
    ([Inflights__Fullⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:201):

      in.count == in.size || (in.maxBytes != 0 && in.bytes >= in.maxBytes)

    It is a function of [iv] and not an existential because [Inflights.Add]
    **panics** when it is [true] ("cannot add into a Full inflights",
    tracker.v:100), so [Add]'s triple can only be stated -- truthfully -- at
    an [Inflights] value the caller knows is not full.  That is why
    [own_inflights] is indexed by the value. *)
Definition inflights_full (iv : tracker.Inflights.t) : bool :=
  bool_decide (iv.(tracker.Inflights.count') = iv.(tracker.Inflights.size'))
  || (bool_decide (iv.(tracker.Inflights.maxBytes') ≠ W64 0) &&
      bool_decide (uint.Z iv.(tracker.Inflights.maxBytes')
                   ≤ uint.Z iv.(tracker.Inflights.bytes'))).

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

(** The one predicate for an [Inflights] object, indexed by its value [iv]
    and the contents [buf] of its ring buffer.  [buf] is in the index
    because [grow] is specified by what it does to the buffer.  A caller
    that does not care writes [∃ iv buf, own_inflights l iv buf].  (Until
    2026-09-23 there were two forms, [own_inflights_at l iv] and the
    existential [own_inflights l], and [grow]/[reset] were stated on raw
    points-tos; notes/decisions.md, "Three layers".) *)
Definition own_inflights (l : loc) (iv : tracker.Inflights.t)
    (buf : list tracker.inflight.t) : iProp Σ :=
    "Hiv" ∷ l ↦ iv ∗
    "Hbuf" ∷ iv.(tracker.Inflights.buffer') ↦* buf ∗
    "Hbuf_cap" ∷ own_slice_cap tracker.inflight.t
                   iv.(tracker.Inflights.buffer') (DfracOwn 1) ∗
    "%Hinfl_ok" ∷ ⌜ inflights_ok iv (Z.of_nat (length buf)) ⌝.

(** *** Per-peer replication progress.

    Ownership is of the whole [Progress] *value*, because [reset]'s [Visit]
    closure overwrites one wholesale
    ([pr <-[tracker.Progress] CompositeLiteral ...]); a predicate over
    selected fields could not justify that write.  What hangs off the value
    is its [Inflights] object.

    A field assignment like [becomeLeader]'s [pr.RecentActive := true] steps
    through [pr ↦ pv] with the generated [AccessStrict] instances and leaves
    [Inflights'] alone, so [own_inflights] survives it untouched. *)
(** The three states a [Progress] may legally be in
    ([StateProbe]/[StateReplicate]/[StateSnapshot] = [W64 0]/[1]/[2],
    new/code/go_etcd_io/raft/v3/tracker.v:47-51).  [Progress.IsPaused]
    **panics** on anything else ("unexpected state", tracker.v:456), and
    [bcastAppend] reaches it on every peer, so this has to be an invariant
    rather than a hope.  It is: [reset]'s [Visit] closure writes a literal
    with no [State] field, i.e. the zero value [StateProbe], and
    [ResetState] -- the only other writer on this path, behind
    [BecomeReplicate] and [BecomeSnapshot] -- is always passed one of the
    three. *)
Definition progress_state_ok (st : tracker.StateType.t) : Prop :=
  st = W64 0 ∨ st = W64 1 ∨ st = W64 2.

(** The one predicate for a [Progress] object, indexed by its value [pv]
    and its [Inflights] value [iv]: [IsPaused]'s answer is a function of
    [State] and [MsgAppFlowPaused], and [SentEntries] reaches
    [Inflights.Add], whose precondition is [inflights_full iv = false].  The
    ring buffer's contents are not in the index: no [Progress] method looks
    at them.  A caller that does not care writes
    [∃ pv iv, own_progress pr pv iv].  (Until 2026-09-23 this was
    [own_progress_at], beside an existential [own_progress pr].) *)
Definition own_progress (pr : loc) (pv : tracker.Progress.t)
                        (iv : tracker.Inflights.t) : iProp Σ :=
    "Hpv" ∷ pr ↦ pv ∗
    "Hinfl" ∷ (∃ buf, own_inflights pv.(tracker.Progress.Inflights') iv buf) ∗
    (** No learners are in scope, so no voter's [Progress] is a learner's.
        Added 2026-09-16 because [wp_raft__promotable] needs it: [promotable]
        returns [pr != nil && !pr.IsLearner && ...], and without this conjunct
        its postcondition [b = bool_decide (id ∈ cfg)] is not derivable.  It is
        preserved by everything that writes a [Progress]: [reset]'s [Visit]
        closure copies [IsLearner] across, and [BecomeReplicate] /
        [RecentActive := true] do not touch it. *)
    "%Hnolearner" ∷ ⌜ pv.(tracker.Progress.IsLearner') = false ⌝ ∗
    "%Hstate_ok" ∷ ⌜ progress_state_ok pv.(tracker.Progress.State') ⌝.



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
    voter set and the domain of the progress map are both [cfg]. *)
Definition own_tracker (tv : tracker.ProgressTracker.t) (votes : gmap w64 bool)
    (prs : gmap w64 loc) : iProp Σ :=
  ∃ (voters_ref : loc) (voters : gmap w64 unit)
    (learners learnersNext : gmap w64 unit),
  "Hvotes" ∷ tv.(tracker.ProgressTracker.Votes') ↦$ votes ∗
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
  "#Hprs" ∷ tv.(tracker.ProgressTracker.Progress') ↦$□ prs ∗
  "Hprogs" ∷ ([∗ map] pr ∈ prs, ∃ pv iv, own_progress pr pv iv) ∗
  "%Hprs_dom" ∷ ⌜ dom prs = cfg ⌝ ∗
  (* a simple configuration: second component of the joint config is nil *)
  "%Hvoters_arr" ∷ ⌜ array.arr
      tv.(tracker.ProgressTracker.Config').(tracker.Config.Voters')
      = [voters_ref; map.nil] ⌝ ∗
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
  (* **The voter set is non-empty.**  Needed because
     [MajorityConfig.VoteResult] returns [VoteWon] *outright* for an empty
     config ([new/code/go_etcd_io/raft/v3/quorum.v:412-418] -- "by
     convention, the elections on an empty config win"), while
     [is_quorum ∅ q] unfolds to [0 < 2 * 0].  So without this,
     [wp_ProgressTracker__TallyVotes]'s [VoteWon] conjunct is **false**;
     found 2026-09-16.  Nothing else here excludes it: [dom prs = cfg] and
     [dom voters = cfg] are both satisfiable at [∅].

     Free to add: no proof in the development *constructs* an [own_tracker]
     from scratch -- every lemma that re-establishes one does so from one it
     was given -- so a new conjunct costs nothing but is preserved
     everywhere.  Like [Hcfg_size] it is a property of the configuration,
     and it is true of any real raft: a node's own id is a voter. *)
  "%Hcfg_ne" ∷ ⌜ cfg ≠ ∅ ⌝ ∗
  (** **The inflight window is a sane size.**  [Config.validate] requires
      [MaxInflightMsgs] to be in [(0, 1<<30]], and [newRaft] copies it into
      the tracker; the bound is [2^62] rather than [1<<30] because that is
      all any proof needs.  Needed because [reset]'s [Visit] closure calls
      [tracker.NewInflights(r.trk.MaxInflight, …)], and the ring-buffer
      invariant of [own_inflights] pins [0 ≤ size < 2^62] (see
      [inflights_ok]).  Like [Hcfg_size] and [Hcfg_ne] it is a property of
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
    with only [own_progress pr] in hand it could not even step the
    [map.lookup1].  Handing it [own_progress pr] *plus* the accessor wand
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
    [own_progress] it is there to overwrite.  So [Visit], which does hold
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
Definition visit_closure (trk : loc) (votes : gmap w64 bool)
  (prs : gmap w64 loc) (f : func.t) (I : iProp Σ) : iProp Σ :=
  ∀ (i : w64) (pr : loc) (tv : tracker.ProgressTracker.t),
    {{{ ⌜ i ∈ cfg ⌝ ∗ ⌜ prs !! i = Some pr ⌝ ∗
        ⌜ (0 ≤ sint.Z tv.(tracker.ProgressTracker.MaxInflight') < 2 ^ 62)%Z ⌝ ∗
        trk ↦ tv ∗ (∃ pv iv, own_progress pr pv iv) ∗
        ((∃ pv iv, own_progress pr pv iv) -∗ own_tracker tv votes prs) ∗ I }}}
      #f #i #pr
    {{{ RET #(); ∃ tv', trk ↦ tv' ∗ own_tracker tv' votes prs ∗ I }}}.


(** The inflight-window bound, read out without consuming the tracker.
    [reset]'s [Visit] closure calls [tracker.NewInflights(r.trk.MaxInflight,
    ...)], whose premise this is; the closure cannot reach [own_tracker]
    itself, so [reset] pulls the fact into the Coq context before the
    [Visit]. *)
Lemma own_tracker_maxinflight tv votes prs :
  own_tracker tv votes prs -∗
  ⌜ (0 ≤ sint.Z tv.(tracker.ProgressTracker.MaxInflight') < 2 ^ 62)%Z ⌝ ∗
  own_tracker tv votes prs.
Proof using All.
  iIntros "Hown". iNamed "Hown".
  iSplitR; first (iPureIntro; exact HmaxInfl).
  rewrite /own_tracker. iExists voters_ref, voters, learners, learnersNext.
  iFrame "∗#%".
Qed.

(** Borrow one voter's [Progress] out of the tracker, by its key in the
    progress map the tracker is indexed by.  The caller can come back to
    the *same* pointer after any call that returns the tracker at the same
    [prs]. *)
Lemma own_tracker_lookup tv votes (prs : gmap w64 loc) (i : w64) (pr : loc) :
  prs !! i = Some pr →
  own_tracker tv votes prs -∗
  (∃ pv iv, own_progress pr pv iv) ∗
  ((∃ pv iv, own_progress pr pv iv) -∗ own_tracker tv votes prs).
Proof using All.
  intros Hpr. iIntros "Hown". iNamed "Hown".
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hpr with "Hprogs") as "[Hpr Hback]".
  iFrame "Hpr".
  iIntros "Hpr". iDestruct ("Hback" with "Hpr") as "Hprogs".
  rewrite /own_tracker.
  iExists voters_ref, voters, learners, learnersNext.
  iFrame "∗#%".
Qed.

(** Read the progress map's points-to and domain out of the tracker without
    consuming it (the map is read-only, hence persistent). *)
Lemma own_tracker_progress_map tv votes prs :
  own_tracker tv votes prs -∗
  tv.(tracker.ProgressTracker.Progress') ↦$□ prs ∗ ⌜ dom prs = cfg ⌝ ∗
  own_tracker tv votes prs.
Proof using All.
  iIntros "Hown". iNamed "Hown".
  iFrame "Hprs". iSplitR; first (iPureIntro; exact Hprs_dom).
  rewrite /own_tracker. iExists voters_ref, voters, learners, learnersNext.
  iFrame "∗#%".
Qed.

(** [trk.Progress[i]], for a voter [i]: [becomeLeader] looks up [r.id].
    Only voters are in the map, whence the side condition. *)
Lemma wp_tracker_progress_lookup tv votes prs (i : w64) :
  i ∈ cfg →
  {{{ own_tracker tv votes prs }}}
    map.lookup1 go.uint64 (go.PointerType tracker.Progress)
      #(tv.(tracker.ProgressTracker.Progress')) #i
  {{{ (pr : loc), RET #pr;
      ⌜ prs !! i = Some pr ⌝ ∗
      (∃ pv iv, own_progress pr pv iv) ∗
      ((∃ pv iv, own_progress pr pv iv) -∗ own_tracker tv votes prs) }}}.
Proof.
  intros Hi. iIntros (Φ) "Hown HΦ". iNamed "Hown".
  assert (is_Some (prs !! i)) as [pr Hpr].
  { apply elem_of_dom. rewrite Hprs_dom //. }
  wp_apply (wp_map_lookup1 with "Hprs") as "_".
  rewrite Hpr /=.
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hpr with "Hprogs") as "[Hpr Hback]".
  iApply ("HΦ" $! pr). iFrame "Hpr". iSplitR; first done.
  iIntros "Hpr". iDestruct ("Hback" with "Hpr") as "Hprogs".
  rewrite /own_tracker.
  iExists voters_ref, voters, learners, learnersNext.
  iFrame "∗#%".
Qed.


End proof.
