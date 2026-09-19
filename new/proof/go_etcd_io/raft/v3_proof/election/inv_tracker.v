(** * The progress tracker and per-peer progress

    Since 2026-09-16 these are **definitions, not axioms**.  The tracker is
    core raft, so it is in scope: the only things this development is allowed
    to assume outright are the ones outside the raft protocol itself (the
    [Logger] interface, the tracing hooks, [slices.Sort], the RNG).  The
    method lemmas below are therefore [Lemma]s -- several still [Admitted],
    which marks them as *in scope and unfinished* rather than assumed. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.defs.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** The (fixed) set of voters. *)
Context (cfg : gset w64).

(** *** Inflights.

    A sliding window of in-flight append sizes.  Election never inspects it:
    [reset] allocates a fresh one per peer, and [maybeSendAppend] only asks
    whether it is full.  So the contents are existential -- what matters is
    that the object and its buffer are owned, so that a [Progress] can be
    overwritten wholesale. *)
Definition own_inflights (l : loc) : iProp Σ :=
  ∃ (iv : tracker.Inflights.t) (buf : list tracker.inflight.t),
    "Hiv" ∷ l ↦ iv ∗
    "Hbuf" ∷ iv.(tracker.Inflights.buffer') ↦* buf ∗
    "Hbuf_cap" ∷ own_slice_cap tracker.inflight.t
                   iv.(tracker.Inflights.buffer') (DfracOwn 1).

(** *** Per-peer replication progress.

    Ownership is of the whole [Progress] *value*, because [reset]'s [Visit]
    closure overwrites one wholesale
    ([pr <-[tracker.Progress] CompositeLiteral ...]); a predicate over
    selected fields could not justify that write.  What hangs off the value
    is its [Inflights] object.

    A field assignment like [becomeLeader]'s [pr.RecentActive := true] steps
    through [pr ↦ pv] with the generated [AccessStrict] instances and leaves
    [Inflights'] alone, so [own_inflights] survives it untouched. *)
Definition own_progress (pr : loc) : iProp Σ :=
  ∃ (pv : tracker.Progress.t),
    "Hpv" ∷ pr ↦ pv ∗
    "Hinfl" ∷ own_inflights pv.(tracker.Progress.Inflights') ∗
    (** No learners are in scope, so no voter's [Progress] is a learner's.
        Added 2026-09-16 because [wp_raft__promotable] needs it: [promotable]
        returns [pr != nil && !pr.IsLearner && ...], and without this conjunct
        its postcondition [b = bool_decide (id ∈ cfg)] is not derivable.  It is
        preserved by everything that writes a [Progress]: [reset]'s [Visit]
        closure copies [IsLearner] across, and [BecomeReplicate] /
        [RecentActive := true] do not touch it. *)
    "%Hnolearner" ∷ ⌜ pv.(tracker.Progress.IsLearner') = false ⌝.

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
  : iProp Σ :=
  ∃ (prs : gmap w64 loc) (voters_ref : loc) (voters : gmap w64 unit)
    (learners learnersNext : gmap w64 unit),
  "Hvotes" ∷ tv.(tracker.ProgressTracker.Votes') ↦$ votes ∗
  "Hprs" ∷ tv.(tracker.ProgressTracker.Progress') ↦$ prs ∗
  "Hprogs" ∷ ([∗ map] pr ∈ prs, own_progress pr) ∗
  "%Hprs_dom" ∷ ⌜ dom prs = cfg ⌝ ∗
  (* a simple configuration: second component of the joint config is nil *)
  "%Hvoters_arr" ∷ ⌜ array.arr
      tv.(tracker.ProgressTracker.Config').(tracker.Config.Voters')
      = [voters_ref; map.nil] ⌝ ∗
  "Hvoters" ∷ voters_ref ↦$ voters ∗
  "%Hvoters_dom" ∷ ⌜ dom voters = cfg ⌝ ∗
  (* no learners *)
  "Hlearners" ∷ tv.(tracker.ProgressTracker.Config').(tracker.Config.Learners')
                  ↦$ learners ∗
  "HlearnersNext" ∷
      tv.(tracker.ProgressTracker.Config').(tracker.Config.LearnersNext')
        ↦$ learnersNext ∗
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
  "%Hcfg_ne" ∷ ⌜ cfg ≠ ∅ ⌝.


(** *** Pure facts about the quorum vocabulary

    [TallyVotes] has to connect what the Go code counts to what the model
    says.  These lemmas are the bridge, and they are pure Rocq -- no program,
    no ownership -- so they are stated here rather than inside a proof.
    [is_quorum], [granted] and [rejected] are from
    [v3_proof/election_protocol.v]. *)

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

    [wp_map_for_range] ([new/golang/theory/map.v:213]) hands the proof an
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
    [trk ↦ tv], and whatever the caller lends it ([I]); it must give all
    three back.  [reset]'s closure needs all three: it overwrites the
    [Progress], reads [r.trk.MaxInflight] and [r.trk.MaxInflightBytes]
    through the field, and reads [r.raftLog] and [r.id] through [I].

    **Why the field is lent rather than kept.**  [Visit] itself reads
    [p.Progress] on every iteration, so it cannot hand the field over for
    good; and the closure reads a *different* sub-field of the same value,
    so it cannot be denied it.  The two reads are at different times, so
    lending resolves it.  See [spec_ProgressTracker__Visit.v] for how this
    was got wrong. *)
Definition visit_closure (trk : loc) (tv : tracker.ProgressTracker.t)
  (f : func.t) (I : iProp Σ) : iProp Σ :=
  ∀ (i : w64) (pr : loc),
    {{{ trk ↦ tv ∗ own_progress pr ∗ I }}}
      #f #i #pr
    {{{ RET #(); trk ↦ tv ∗ own_progress pr ∗ I }}}.


(** [trk.Progress[i]], for a voter [i]: [becomeLeader] looks up [r.id].
    Only voters are in the map, whence the side condition. *)
Lemma wp_tracker_progress_lookup tv votes (i : w64) :
  i ∈ cfg →
  {{{ own_tracker tv votes }}}
    map.lookup1 go.uint64 (go.PointerType tracker.Progress)
      #(tv.(tracker.ProgressTracker.Progress')) #i
  {{{ (pr : loc), RET #pr;
      own_progress pr ∗ (own_progress pr -∗ own_tracker tv votes) }}}.
Proof.
  intros Hi. iIntros (Φ) "Hown HΦ". iNamed "Hown".
  assert (is_Some (prs !! i)) as [pr Hpr].
  { apply elem_of_dom. rewrite Hprs_dom //. }
  wp_apply (wp_map_lookup1 with "Hprs") as "Hprs".
  rewrite Hpr /=.
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hpr with "Hprogs") as "[Hpr Hback]".
  iApply ("HΦ" $! pr). iFrame "Hpr".
  iIntros "Hpr". iDestruct ("Hback" with "Hpr") as "Hprogs".
  rewrite /own_tracker.
  iExists prs, voters_ref, voters, learners, learnersNext.
  iFrame "∗%".
Qed.


End proof.
