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

(** [ResetVotes] assigns a fresh empty map to [p.Votes], so it changes the
    tracker value as well as the heap it points at. *)
Lemma wp_ProgressTracker__ResetVotes (trk : loc) tv votes :
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker tv votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "ResetVotes" #()
  {{{ (votesRef : loc), RET #();
      trk ↦ (tv <| tracker.ProgressTracker.Votes' := votesRef |>) ∗
      own_tracker (tv <| tracker.ProgressTracker.Votes' := votesRef |>) ∅ }}}.
Proof.
  wp_start as "[Htrk Hown]". iNamed "Hown". wp_auto.
  wp_apply wp_map_make1. iIntros "%votesRef Hvotes_new". wp_auto.
  iApply ("HΦ" $! votesRef). iFrame "Htrk".
  rewrite /own_tracker /=.
  iExists prs, voters_ref, voters, learners, learnersNext.
  iFrame "Hvotes_new". iFrame "∗%".
Qed.

(** [RecordVote] only inserts into the map [p.Votes] already refers to, so
    the tracker value is unchanged.  First write wins, which is [record_vote]. *)
Lemma wp_ProgressTracker__RecordVote (trk : loc) tv votes (from : w64) (v : bool) :
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker tv votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "RecordVote" #from #v
  {{{ RET #(); trk ↦ tv ∗ own_tracker tv (record_vote votes from v) }}}.
Proof.
  wp_start as "[Htrk Hown]". iNamed "Hown". wp_auto.
  wp_apply (wp_map_lookup2 with "Hvotes") as "Hvotes".
  case_bool_decide as Hok.
  - (* already voted: first write wins, the map is left alone *)
    wp_auto.
    iApply "HΦ". iFrame "Htrk".
    destruct Hok as [v0 Hv0].
    rewrite /own_tracker /record_vote Hv0 /=.
    iExists prs, voters_ref, voters, learners, learnersNext.
    iFrame "∗%".
  - (* first vote from [from] *)
    wp_auto.
    apply eq_None_not_Some in Hok.
    (* no trailing [wp_auto]: [wp_apply … as] already ran it -- gotchas.md *)
    wp_apply (wp_map_insert with "Hvotes") as "Hvotes".
    iApply "HΦ". iFrame "Htrk".
    rewrite /own_tracker /record_vote Hok /=.
    iExists prs, voters_ref, voters, learners, learnersNext.
    iFrame "∗%".
Qed.

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
  wp_start as "Hm".
  rewrite (go.len_underlying tracker.ProgressMap).
  rewrite (go.is_underlying (t := tracker.ProgressMap)
             (tunder := go.MapType go.uint64 (go.PointerType tracker.Progress))).
  (* [wp_start]'s [wp_func_call] ran before the rewrite, so redo it. *)
  wp_func_call. wp_call.
  rewrite own_map_unseal. iNamed "Hm".
  wp_apply (_internal_wp_untyped_read with "Hown") as "Hown".
  destruct (go.is_map_domain_exists _ _ His_map) as [ks Hks].
  pose proof (go.internal_map_length_step_pure mv ks Hks) as Hlenstep.
  wp_auto.
  (* [length ks = size m]: the argument [wp_map_for_range] makes internally,
     and the same one [proof_raft__campaign.v]'s [wp_map_len_uint64] makes. *)
  assert (length ks = size m) as ->.
  { eapply go.is_map_domain_pure in Hks; last exact His_map.
    destruct Hks as [Hnodup Hiff].
    assert (Forall (λ kv, ∃ (k : w64), kv = #k) ks) as Heq.
    { rewrite Forall_forall. intros kv. rewrite -list_elem_of_In.
      intros Hk. apply Hdom. by apply Hiff. }
    apply Forall_exists_Forall2_l in Heq as [keys Heq].
    apply Forall2_fmap_2 in Heq. rewrite -list_eq_Forall2 in Heq.
    rewrite list_fmap_id in Heq. subst.
    assert (list_to_set keys = dom m) as Hl.
    { rewrite sets.set_eq. intros k. rewrite elem_of_list_to_set.
      specialize (Hiff #k). specialize (Hagree k).
      rewrite list_elem_of_fmap_inj in Hiff.
      rewrite -Hiff Hagree elem_of_dom. by destruct lookup. }
    apply NoDup_fmap in Hnodup; last tc_solve.
    rewrite length_fmap.
    rewrite <- (size_list_to_set (C:=gset w64)); last done.
    rewrite Hl size_dom //. }
  iApply "HΦ". iFrame "∗%".
Qed.

(** [TallyVotes] reports the outcome of the election, which is exactly the
    quorum condition of the model.

    **In scope, and blocked on the *translation*, not on the proof**
    (2026-09-16).  Everything down to the [Admitted] is machine-checked
    ([rocq compile -vok] over a scratch module holding this identical
    script, RC=0): the whole tally loop over [trk.Progress] is proved, and
    the program is parked on the function's last statement,
    [p.Config.Voters.VoteResult(p.Votes)].

    What blocks it is the **same defect** that blocks [wp_campaign_peer_ids]
    ([inv_misc.v], which has the full write-up and the three probes).
    [quorum.JointConfig] is [[2]MajorityConfig], an *array*, and Goose
    translates the element reads [c[0]] / [c[1]] inside
    [JointConfig.VoteResult] ([new/code/.../quorum.v:154,158]) as

        MethodResolve (go.PointerType MajorityConfig) "VoteResult"
          (IndexRef JointConfig (![JointConfig] "c", #(W64 0)))

    -- [IndexRef] applied to the array *value*, where [index_ref_array]
    ([new/golang/defn/array.v:50]) only steps on an array *location*.
    Confirmed here too, by stepping [JointConfig.VoteResult] on its own:

        Lemma probe (l : loc) (jc : quorum.JointConfig.t) (vref : loc) votes :
          {{{ is_pkg_init quorum ∗ l ↦ jc ∗ vref ↦$ votes }}}
            l @! (go.PointerType quorum.JointConfig) @! "VoteResult" #vref
          {{{ (r : w8), RET #r; True }}}.
        Proof.
          wp_start as "(Hl & Hv)". wp_auto.
          wp_method_call. wp_call.
          rewrite /quorum.JointConfig__VoteResultⁱᵐᵖˡ. wp_auto.
          (* parks with [IndexRef quorum.JointConfig (# jc, # (W64 0))] *)
        Admitted.

    There is a **second** obstacle on the same statement, which the array fix
    alone would not clear: the second component of the joint config is
    [map.nil] ([Hvoters_arr]), and [MajorityConfig.VoteResult] begins with
    [len(c) == 0].  [len] of a nil map unfolds to [InternalMapLength (Read
    #map.nil)] -- a read of the null location -- and there is no nil-map
    instance for [go.len] the way there is one for ranging
    ([wp_map_nil_for_range], [new/golang/theory/map.v:305]).  Not probed; flagged
    so the next attempt measures it before assuming it works.

    **The [VoteWon] conjunct is false when [cfg = ∅], and that is not fixed
    by unblocking the translation.**  [MajorityConfig.VoteResult] returns
    [VoteWon] outright when [len(c) == 0] ("by convention, the elections on
    an empty config win", [new/code/.../quorum.v:416-418]), while
    [is_quorum ∅ q] unfolds to [0 < 2 * 0], which is [False].  Nothing in
    [own_tracker] rules [cfg = ∅] out: [dom prs = cfg] and [dom voters = cfg]
    are both satisfiable at [∅].  The fix is a [⌜ cfg ≠ ∅ ⌝] conjunct in
    [own_tracker] -- a *strengthening* of a predicate that no proof
    constructs from scratch, so it costs nothing to add and it is preserved
    by every method here -- not a weakening of this statement.  It was left
    undone because the lemma is unprovable anyway and adding it would have
    touched files outside this one's blast radius.

    **What remains once [IndexRef] steps**, in terms of what is already
    proved below: the joint result is [r1], the [MajorityConfig.VoteResult]
    of [voters_ref], because [r2] is the empty config's [VoteWon] and
    [JointConfig.VoteResult] returns [r1] when [r1 = r2], [VoteLost] when
    either is [VoteLost], and [VotePending] otherwise.  In
    [MajorityConfig.VoteResult] over [voters_ref] ([dom voters = cfg]):
    [votedCnt = size (granted votes ∩ cfg)] and
    [missing = size (cfg ∖ dom votes)], each a [wp_map_for_range] with an
    [nsat] invariant exactly like the one below, discharged by [nsat_granted]
    and [nsat_missing].  Then [q = size cfg / 2 + 1], so
    [votedCnt ≥ q ↔ is_quorum cfg (granted votes)] by [is_quorum_alt], and
    [votedCnt + missing < q ↔ ¬ is_quorum cfg (cfg ∖ rejected votes)] by
    [is_quorum_alt] together with [size_cfg_minus_rejected].  That is the
    whole of both postcondition conjuncts; the pure half of the argument is
    already machine-checked above. *)
Lemma wp_ProgressTracker__TallyVotes (trk : loc) tv votes :
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker tv votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "TallyVotes" #()
  {{{ (g rj : w64) (res : w8), RET (#g, #rj, #res);
      trk ↦ tv ∗ own_tracker tv votes ∗
      ⌜ res = VoteWon ∨ res = VoteLost ∨ res = VotePending ⌝ ∗
      ⌜ res = VoteWon → is_quorum cfg (granted votes) ⌝ ∗
      (* [VoteLost] means the candidate **cannot still win**, not that a
         majority rejected -- Go computes [votedCnt + missing < q], and
         [votedCnt + missing = size (cfg ∖ rejected)].  The old form,
         [is_quorum cfg (rejected votes)], was false: 4 voters with 2
         rejecting and 2 silent gives [VoteLost] with no rejection quorum.
         Corrected 2026-09-16; see election_protocol.v's [step_lose]. *)
      ⌜ res = VoteLost → ¬ is_quorum cfg (cfg ∖ rejected votes) ⌝ }}}.
Proof.
  (* Everything down to the [Admitted] is machine-checked. *)
  wp_start as "(Htrk & Hown)". iNamed "Hown".
  (* the [var _ quorum.VoteResult] declaration Go emits for the named return
     is an *anonymous* [GoAlloc], which [wp_auto] will not step past. *)
  wp_alloc res0 as "Hres0". wp_auto.
  set (Pgr := (λ k, votes !! k = Some true) : w64 → Prop).
  set (Prj := (λ k, votes !! k = Some false) : w64 → Prop).
  (* [pr] and [id] are the range's own loop variables: the body assigns them
     on every iteration, so they must be existentially quantified *inside*
     the invariant -- the same trap [proof_raft__campaign.v] documents for
     [slice.for_range]. *)
  set (Pmap := (λ (keys : list w64) (i : Z),
    ∃ (prv : loc) (idv : w64),
      "%Hi" ∷ ⌜ 0 ≤ i ⌝ ∗
      "Htrk" ∷ trk ↦ tv ∗
      "Hvotes" ∷ tv.(tracker.ProgressTracker.Votes') ↦$ votes ∗
      "Hprogs" ∷ ([∗ map] pr ∈ prs, own_progress pr) ∗
      "p" ∷ p_ptr ↦ trk ∗
      "pr" ∷ pr_ptr ↦ prv ∗
      "id" ∷ id_ptr ↦ idv ∗
      "granted" ∷ granted_ptr ↦ W64 (nsat Pgr (take (Z.to_nat i) keys)) ∗
      "rejected" ∷ rejected_ptr ↦ W64 (nsat Prj (take (Z.to_nat i) keys)))%I).
  wp_apply (wp_map_for_range Pmap with "Hprs").
  iIntros (keys) "(%Hkset & %Hklen & %Hknodup)".
  iSplitL "Htrk Hvotes Hprogs p pr id granted rejected".
  { rewrite /Pmap. iExists null, (W64 0).
    rewrite take_0 /nsat filter_nil /=. iFrame. iPureIntro. lia. }
  iSplitL "".
  { iIntros "!>" (i key prl) "[%Hkey %Hprl] HP". rewrite /Pmap. iNamed "HP".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hprl with "Hprogs") as "[Hpr Hback]".
    iNamed "Hpr".
    assert (Z.to_nat (i + 1) = S (Z.to_nat i)) as Hsucc.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal. all: lia. }
    assert (take (Z.to_nat (i + 1)) keys = take (Z.to_nat i) keys ++ [key])
      as Htake.
    { rewrite Hsucc. by apply take_S_r. }
    assert (size prs = size cfg) as Hszprs by (rewrite -Hprs_dom size_dom //).
    (* the counters are bounded by [size cfg], which is what lets [word] see
       that [granted + 1] does not wrap *)
    assert (nsat Pgr (take (Z.to_nat i) keys) ≤ size cfg)%nat as HgB.
    { etrans; first apply nsat_le. rewrite length_take Hklen Hszprs. lia. }
    assert (nsat Prj (take (Z.to_nat i) keys) ≤ size cfg)%nat as HrB.
    { etrans; first apply nsat_le. rewrite length_take Hklen Hszprs. lia. }
    wp_auto.
    (* [if pr.IsLearner { continue }]: no voter is a learner, and without
       [Hnolearner] the [if] scrutinee is not a literal and [wp_auto] parks. *)
    rewrite Hnolearner. wp_auto.
    wp_apply (wp_map_lookup2 with "Hvotes"). iIntros "Hvotes".
    iDestruct ("Hback" with "[Hpv Hinfl]") as "Hprogs".
    { rewrite /own_progress. iExists _. iFrame. done. }
    destruct (votes !! key) as [[|]|] eqn:Hvk.
    - (* granted *)
      assert (Pgr key) as HPg by (rewrite /Pgr Hvk //).
      assert (¬ Prj key) as HPr by (rewrite /Prj Hvk; congruence).
      rewrite bool_decide_eq_true_2; last by eexists.
      wp_auto.
      iRight. iLeft. iSplit; first done.
      iExists prl, key. rewrite Htake !nsat_snoc.
      destruct (decide (Pgr key)); last done.
      destruct (decide (Prj key)); first done.
      rewrite Nat.add_0_r.
      replace (W64 (nsat Pgr (take (Z.to_nat i) keys) + 1)%nat)
        with (word.add (W64 (nsat Pgr (take (Z.to_nat i) keys))) (W64 1))
        by word.
      iFrame. iPureIntro. lia.
    - (* rejected *)
      assert (¬ Pgr key) as HPg by (rewrite /Pgr Hvk; congruence).
      assert (Prj key) as HPr by (rewrite /Prj Hvk //).
      rewrite bool_decide_eq_true_2; last by eexists.
      wp_auto.
      iRight. iLeft. iSplit; first done.
      iExists prl, key. rewrite Htake !nsat_snoc.
      destruct (decide (Pgr key)); first done.
      destruct (decide (Prj key)); last done.
      rewrite Nat.add_0_r.
      replace (W64 (nsat Prj (take (Z.to_nat i) keys) + 1)%nat)
        with (word.add (W64 (nsat Prj (take (Z.to_nat i) keys))) (W64 1))
        by word.
      iFrame. iPureIntro. lia.
    - (* this voter has not answered: [continue], both counters unchanged *)
      assert (¬ Pgr key) as HPg by (rewrite /Pgr Hvk; congruence).
      assert (¬ Prj key) as HPr by (rewrite /Prj Hvk; congruence).
      rewrite bool_decide_eq_false_2; last by intros [? ?].
      wp_auto.
      iLeft. iSplit; first done.
      iExists prl, key. rewrite Htake !nsat_snoc.
      destruct (decide (Pgr key)); first done.
      destruct (decide (Prj key)); first done.
      rewrite !Nat.add_0_r.
      iFrame. iPureIntro. lia. }
  (* the range is over, so the counters hold the whole tally *)
  iIntros "HP". rewrite /Pmap. iNamed "HP".
  rewrite Nat2Z.id -Hklen firstn_all.
  assert ((list_to_set keys : gset w64) = cfg) as Hkcfg
    by (rewrite Hkset Hprs_dom //).
  assert (nsat Pgr keys = size (granted votes ∩ cfg)) as Hgfin.
  { rewrite /Pgr. by apply nsat_granted. }
  assert (nsat Prj keys = size (rejected votes ∩ cfg)) as Hrfin.
  { rewrite /Prj. by apply nsat_rejected. }
  wp_auto.
  (* STUCK, and this is the real stuck point.  The remaining program is

       let: "$r0" := ((trk.[ProgressTracker.t,"Config"]).[Config.t,"Voters"])
                       @! (go.PointerType quorum.JointConfig) @! "VoteResult"
                         (# tv.(ProgressTracker.Votes')) in
       (do: # result_ptr <-[quorum.VoteResult] "$r0") ;;;
       return: (![go.int] (# granted_ptr), ![go.int] (# rejected_ptr),
                ![quorum.VoteResult] (# result_ptr))

     with ["granted" ∷ granted_ptr ↦ W64 (nsat Pgr keys)] and
     ["rejected" ∷ rejected_ptr ↦ W64 (nsat Prj keys)] in hand, and [Hgfin] /
     [Hrfin] identifying those counts with the model's.  See the note above
     the statement for why the call cannot be stepped. *)
Admitted.

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
    lending resolves it.  See the note on
    [wp_ProgressTracker__Visit] below for how this was got wrong. *)
Definition visit_closure (trk : loc) (tv : tracker.ProgressTracker.t)
  (f : func.t) (I : iProp Σ) : iProp Σ :=
  ∀ (i : w64) (pr : loc),
    {{{ trk ↦ tv ∗ own_progress pr ∗ I }}}
      #f #i #pr
    {{{ RET #(); trk ↦ tv ∗ own_progress pr ∗ I }}}.

(** **This statement was FALSE until 2026-09-16** and is now repaired.  The
    repair is recorded here rather than silently applied, because a [Qed]
    resting on a false [Admitted] is unsound and [proof_raft__reset.v] --
    hence [becomeFollower], [becomeCandidate], [becomeLeader] and everything
    above them -- was resting on this one.

    **What was wrong.**  The precondition owned no part of the tracker
    *struct*.  [own_tracker tv votes] is indexed by the tracker *value* and
    owns what that value points at -- the vote map, the progress map, the id
    sets -- not the bytes of [trk] itself.  But [Visit] has a pointer
    receiver and its very first statement is [n := len(p.Progress)], which
    Goose translates to

        ![tracker.ProgressMap]
          (StructFieldRef ProgressTracker "Progress"
             (![go.PointerType ProgressTracker] "p"))

    -- a load through [trk.[ProgressTracker.t, "Progress"]]
    ([new/code/go_etcd_io/raft/v3/tracker.v:809]).  It reads that field again
    inside the second range, for the [map.lookup1] that produces each [pr]
    ([tracker.v:837]).  So the triple asserted safety of a load from a
    location it did not own.  Measured with two probes, each
    [rocq compile -vok] RC=0:

      - precondition as it was: [wp_start; iNamed "Hown"; wp_auto] parks
        immediately, with the whole body still to run;
      - precondition plus [trk ↦ tv]: the same three tactics get through the
        receiver alloc, the field load and the [len] call's argument.

    The comment that used to sit here claimed "[Visit] reads the progress map
    out of the tracker value it is given and does not mutate the tracker
    itself, so it does not need the location".  The second half is true and
    the first is not -- it reads the map *reference* out of the struct,
    through the pointer.  Mutation was never the question; any read through
    the receiver is.  An invariant promised in prose and absent from the
    conjuncts, which is the same failure as the [r.step] one; see
    notes/STATUS.md's table.

    **The repair**, applied: [trk ↦ tv] in the pre- and postcondition, and
    lent to the closure as well ([visit_closure trk tv f I], above).  Lending
    is necessary, not cosmetic -- see that definition's comment.
    [proof_raft__reset.v] keeps the field split out with its
    [raft_split_trk] instead of re-assembling it after [ResetVotes], and its
    closure applies the continuation wand to read [r.trk.MaxInflight] and
    re-splits before returning.

    **The statement is now true but still unprovable**, for two reasons that
    have nothing to do with raft.  Both are filed in
    bugs/goose-array-indexref-loads-its-operand.md:

    1. [var sl [7]uint64; if len(sl) >= n] asks for [len] of an *array*, and
       there is **no** [FuncUnfold go.len [go.ArrayType n t]] instance
       anywhere under [new/golang/].  [go.len_underlying] does not help: an
       array type is already its own underlying type.  [wp_auto] parks on a
       bare [#(functions go.len [go.ArrayType 7 go.uint64])].  (Contrast
       maps, where the instance exists but only at the literal [go.MapType];
       [wp_ProgressMap_len] above is that workaround.)
    2. [ids = sl[:n]] is translated as [Slice] applied to the array *value*
       ([tracker.v:816]), where [slice_array_step]
       ([new/golang/defn/array.v:80]) steps only on an array *location*.

    The [else] branch ([make([]uint64, n)], taken when [size cfg > 7]) is
    fine; only the fast path is stuck.

    Nothing about the *proof* is hard once the code steps: a
    [wp_map_for_range] filling [ids] backwards from [n-1], [wp_slices_Sort]
    ([inv_slices.v]) for the permutation, then a [slice.for_range] applying
    [visit_closure] to each id with [big_sepM_lookup_acc] on [Hprogs].  The
    sorted order is not observable -- no caller's [I] mentions it -- so the
    permutation-only postcondition of [wp_slices_Sort] is enough. *)
Lemma wp_ProgressTracker__Visit (trk : loc) tv votes (f : func.t) (I : iProp Σ) :
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker tv votes ∗ I ∗
      □ visit_closure trk tv f I }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "Visit" #f
  {{{ RET #(); trk ↦ tv ∗ own_tracker tv votes ∗ I }}}.
Proof.
  (* Machine-checked as far as it goes.  With [trk ↦ tv] in hand the receiver
     alloc, the [p.Progress] load and the [len] call's argument all step --
     that is the part the old precondition could not reach at all.  It parks
     on [len] of the [[7]uint64] array, for which no instance exists; see (1)
     in the note above. *)
  wp_start as "(Htrk & Hown & HI & #Hf)". iNamed "Hown". wp_auto.
  (* [n := len(p.Progress)].  No [wp_auto] after this: the next statement is
     [len] of the [[7]uint64] array and it has no instance, so [wp_auto]
     fails with "Failed to progress" rather than parking. *)
  wp_apply (wp_ProgressMap_len with "[$Hprs]") as "Hprs".
Admitted.

(** [NewInflights] allocates one. *)
Lemma wp_tracker_NewInflights (size maxBytes : w64) :
  {{{ is_pkg_init tracker }}}
    @! tracker.NewInflights #size #maxBytes
  {{{ (l : loc), RET #l; own_inflights l }}}.
Proof.
  wp_start as "_". wp_auto.
  (* [wp_auto] does not step a [GoAlloc] sitting in [return:] position -- the
     goal is still [WP exception_do (return: GoAlloc tracker.Inflights #{|…|})].
     Allocate explicitly.  The literal leaves [buffer' := slice.nil], so the
     buffer is the empty slice. *)
  wp_apply wp_alloc. iIntros (l) "Hl". wp_auto.
  iApply "HΦ". rewrite /own_inflights /=.
  iExists _, []. iFrame "Hl".
  iSplitL; [iApply own_slice_nil | iApply own_slice_cap_nil].
Qed.

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

(** *** Two internal helpers on the way to [BecomeReplicate].

    Both are stated over the *field* points-tos rather than over
    [own_progress] / [own_inflights], because the caller's [wp_auto] has to
    keep stepping through field reads after the call returns and cannot see
    through an opaque predicate (see notes/gotchas.md). *)
Lemma wp_Inflights__reset (l : loc) (iv : tracker.Inflights.t) :
  {{{ is_pkg_init tracker ∗ l ↦ iv }}}
    l @! (go.PointerType tracker.Inflights) @! "reset" #()
  {{{ RET #(); l ↦ (iv <| tracker.Inflights.start' := W64 0 |>
                       <| tracker.Inflights.count' := W64 0 |>
                       <| tracker.Inflights.bytes' := W64 0 |>) }}}.
Proof. wp_start as "Hl". wp_auto. iApply "HΦ". iFrame. Qed.

Lemma wp_Progress__ResetState (pr : loc) (pv : tracker.Progress.t)
  (iv : tracker.Inflights.t) (st : tracker.StateType.t) :
  {{{ is_pkg_init tracker ∗ pr ↦ pv ∗ pv.(tracker.Progress.Inflights') ↦ iv }}}
    pr @! (go.PointerType tracker.Progress) @! "ResetState" #st
  {{{ RET #();
      pr ↦ (pv <| tracker.Progress.MsgAppFlowPaused' := false |>
               <| tracker.Progress.PendingSnapshot' := W64 0 |>
               <| tracker.Progress.State' := st |>) ∗
      pv.(tracker.Progress.Inflights') ↦ (iv
             <| tracker.Inflights.start' := W64 0 |>
             <| tracker.Inflights.count' := W64 0 |>
             <| tracker.Inflights.bytes' := W64 0 |>) }}}.
Proof.
  wp_start as "[Hpv Hiv]". wp_auto.
  wp_apply (wp_Inflights__reset with "[$Hiv]") as "Hiv".
  iApply "HΦ". iFrame.
Qed.

(** [pr.BecomeReplicate()] moves a [Progress] into the replicating state.
    It says nothing about votes, terms or roles, so the model does not see
    it. *)
Lemma wp_Progress__BecomeReplicate (pr : loc) :
  {{{ is_pkg_init tracker ∗ own_progress pr }}}
    pr @! (go.PointerType tracker.Progress) @! "BecomeReplicate" #()
  {{{ RET #(); own_progress pr }}}.
Proof.
  wp_start as "Hpr". iNamed "Hpr". iNamed "Hinfl". wp_auto.
  wp_apply (wp_Progress__ResetState with "[$Hpv $Hiv]") as "[Hpv Hiv]".
  iApply "HΦ". rewrite /own_progress /own_inflights /=.
  (* after [iExists _] and framing [Hpv] the goal is [Hinfl ∗ %Hnolearner],
     a separating conjunction -- [iExists] cannot apply to it, so split
     first.  [ResetState] carries [IsLearner'] across unchanged, which is
     what discharges the new conjunct. *)
  iExists _. iFrame "Hpv".
  iSplitL "Hiv Hbuf Hbuf_cap".
  (* Do not give the witness: [ResetState] resets the [Inflights] too
     (start/count/bytes zeroed), so it is neither [iv] nor anything already
     named.  Let [iFrame] instantiate the existential from the hypotheses. *)
  (* [simpl] first: the goal's [{|…|}.(Inflights')] projection must reduce to
     [pv.(Inflights')] before [iFrame] can match.  And frame [Hiv] *first*, so
     it fixes the existential to the reset [Inflights] value -- framing [Hbuf]
     first pins the witness to the pre-reset [iv] and then [Hiv] no longer
     matches.  ([Inflights.reset] keeps [buffer'], so [Hbuf]/[Hbuf_cap] fit
     either way.) *)
  { simpl. iFrame "Hiv". iFrame. }
  iPureIntro. exact Hnolearner.
Qed.

End proof.
