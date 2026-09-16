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
    "Hinfl" ∷ own_inflights pv.(tracker.Progress.Inflights').

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
Proof. Admitted.

(** [RecordVote] only inserts into the map [p.Votes] already refers to, so
    the tracker value is unchanged.  First write wins, which is [record_vote]. *)
Lemma wp_ProgressTracker__RecordVote (trk : loc) tv votes (from : w64) (v : bool) :
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker tv votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "RecordVote" #from #v
  {{{ RET #(); trk ↦ tv ∗ own_tracker tv (record_vote votes from v) }}}.
Proof. Admitted.

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
Proof. Admitted.

(** [trk.Progress[i]], for a voter [i]: [becomeLeader] looks up [r.id].
    Only voters are in the map, whence the side condition. *)
Lemma wp_tracker_progress_lookup tv votes (i : w64) :
  i ∈ cfg →
  {{{ own_tracker tv votes }}}
    map.lookup1 go.uint64 (go.PointerType tracker.Progress)
      #(tv.(tracker.ProgressTracker.Progress')) #i
  {{{ (pr : loc), RET #pr;
      own_progress pr ∗ (own_progress pr -∗ own_tracker tv votes) }}}.
Proof. Admitted.

(** [pr.BecomeReplicate()] moves a [Progress] into the replicating state.
    It says nothing about votes, terms or roles, so the model does not see
    it. *)
Lemma wp_Progress__BecomeReplicate (pr : loc) :
  {{{ is_pkg_init tracker ∗ own_progress pr }}}
    pr @! (go.PointerType tracker.Progress) @! "BecomeReplicate" #()
  {{{ RET #(); own_progress pr }}}.
Proof. Admitted.

End proof.
