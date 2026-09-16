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
  "%Hcfg_size" ∷ ⌜ Z.of_nat (size cfg) < 2 ^ 63 ⌝.

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

(** [TallyVotes] reports the outcome of the election, which is exactly the
    quorum condition of the model. *)
Lemma wp_ProgressTracker__TallyVotes (trk : loc) tv votes :
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker tv votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "TallyVotes" #()
  {{{ (g rj : w64) (res : w8), RET (#g, #rj, #res);
      trk ↦ tv ∗ own_tracker tv votes ∗
      ⌜ res = VoteWon ∨ res = VoteLost ∨ res = VotePending ⌝ ∗
      ⌜ res = VoteWon → is_quorum cfg (granted votes) ⌝ ∗
      ⌜ res = VoteLost → is_quorum cfg (rejected votes) ⌝ }}}.
Proof. Admitted.

(** [trk.Visit f] calls [f id pr] on every voter's [Progress].

    The closure is handed full ownership of one [Progress] plus whatever the
    caller lends it ([I]), and must give both back.  [reset]'s closure needs
    both halves: it overwrites the [Progress] and reads [r.raftLog] and
    [r.id] through [I].

    **No [trk ↦ tv].**  [Visit] reads the progress map out of the tracker
    value it is given and does not mutate the tracker itself, so it does not
    need the location -- same as [wp_tracker_progress_lookup] below, and
    unlike [ResetVotes]/[RecordVote], which do mutate.  That matters here:
    [reset]'s closure reads [r.trk.MaxInflight], so the caller must pass the
    whole raft struct as [I], and [r ↦ rv] already covers the [trk] field's
    bytes. *)
Definition visit_closure (f : func.t) (I : iProp Σ) : iProp Σ :=
  ∀ (i : w64) (pr : loc),
    {{{ own_progress pr ∗ I }}}
      #f #i #pr
    {{{ RET #(); own_progress pr ∗ I }}}.

Lemma wp_ProgressTracker__Visit (trk : loc) tv votes (f : func.t) (I : iProp Σ) :
  {{{ is_pkg_init tracker ∗ own_tracker tv votes ∗ I ∗ □ visit_closure f I }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "Visit" #f
  {{{ RET #(); own_tracker tv votes ∗ I }}}.
Proof. Admitted.

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
