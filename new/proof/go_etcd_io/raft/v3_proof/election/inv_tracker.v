(** * The progress tracker and per-peer progress *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.defs.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** The (fixed) set of voters. *)
Context (cfg : gset w64).

(** *** The progress tracker.

    [trk] is embedded in the [raft] struct **by value**, so the tracker's own
    bytes are part of the [r ↦ rv] clause of [own_raft_phys] and must not be
    claimed a second time.  [own_tracker tv votes] therefore owns what the
    tracker *value* [tv] points at, and nothing else: the vote map at
    [tv.Votes], the [Progress] map at [tv.Progress] together with the
    [Progress] objects in it, and the id sets of [tv.Config].  [votes] is the
    recorded vote tally; the voter set is [cfg] (no learners, no joint
    configuration).  Same rule as [own_raft_misc] below — index it by what it
    actually covers.

    The methods need the tracker's *location* too, and [ResetVotes] replaces
    the [Votes] field outright, so they take [trk ↦ tv] as well.  A caller
    holding the whole raft struct splits that field out with

      iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=) in "Hr"

    which turns [r ↦ rv] into the named conjunction of its field
    points-tos, of which [trk] is one. *)
Axiom own_tracker : tracker.ProgressTracker.t → gmap w64 bool → iProp Σ.

(** [ResetVotes] assigns a fresh empty map to [p.Votes], so it changes the
    tracker value as well as the heap it points at. *)
Axiom wp_ProgressTracker__ResetVotes : ∀ (trk : loc) tv votes,
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker tv votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "ResetVotes" #()
  {{{ (votesRef : loc), RET #();
      trk ↦ (tv <| tracker.ProgressTracker.Votes' := votesRef |>) ∗
      own_tracker (tv <| tracker.ProgressTracker.Votes' := votesRef |>) ∅ }}}.

(** [RecordVote] only inserts into the map [p.Votes] already refers to, so
    the tracker value is unchanged. *)
Axiom wp_ProgressTracker__RecordVote : ∀ (trk : loc) tv votes (from : w64) (v : bool),
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker tv votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "RecordVote" #from #v
  {{{ RET #(); trk ↦ tv ∗ own_tracker tv (record_vote votes from v) }}}.

(** [TallyVotes] reports the outcome of the election, which is exactly the
    quorum condition of the model. *)
Axiom wp_ProgressTracker__TallyVotes : ∀ (trk : loc) tv votes,
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker tv votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "TallyVotes" #()
  {{{ (g rj : w64) (res : w8), RET (#g, #rj, #res);
      trk ↦ tv ∗ own_tracker tv votes ∗
      ⌜ res = VoteWon ∨ res = VoteLost ∨ res = VotePending ⌝ ∗
      ⌜ res = VoteWon → is_quorum cfg (granted votes) ⌝ ∗
      ⌜ res = VoteLost → is_quorum cfg (rejected votes) ⌝ }}}.

(** *** Per-peer replication progress.

    [becomeLeader] is the only place on the election path that touches a
    [Progress]: it marks its own replicating and recently active.  Neither
    fact is visible in the model, so a [Progress] is opaque apart from the
    one field the code assigns to directly, which has to be real ownership
    for the assignment to step.

    The [Progress] map and the objects in it are part of [own_tracker]
    above; what is added here is a handle on one of them. *)
Axiom own_progress_rest : loc → iProp Σ.

Definition own_progress (pr : loc) : iProp Σ :=
  ∃ (recentActive : bool),
    struct_field_ref tracker.Progress.t "RecentActive"%go pr ↦ recentActive ∗
    own_progress_rest pr.

(** [trk.Progress[i]], for a voter [i]: [becomeLeader] looks up [r.id].
    Only voters are in the map, whence the side condition.  No [trk ↦ tv]
    here: the lookup reads the map reference out of the value it is given,
    and the caller gets that by reading the struct field itself. *)
Axiom wp_tracker_progress_lookup : ∀ tv votes (i : w64),
  i ∈ cfg →
  {{{ own_tracker tv votes }}}
    map.lookup1 go.uint64 (go.PointerType tracker.Progress)
      #(tv.(tracker.ProgressTracker.Progress')) #i
  {{{ (pr : loc), RET #pr;
      own_progress pr ∗ (own_progress pr -∗ own_tracker tv votes) }}}.

(** [pr.BecomeReplicate()] moves a [Progress] into the replicating state.
    It says nothing about votes, terms or roles, so the model does not see
    it. *)
Axiom wp_Progress__BecomeReplicate : ∀ (pr : loc),
  {{{ is_pkg_init tracker ∗ own_progress pr }}}
    pr @! (go.PointerType tracker.Progress) @! "BecomeReplicate" #()
  {{{ RET #(); own_progress pr }}}.

End proof.
