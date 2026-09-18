Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [r.promotable()]: true exactly when this node is a voter.  It reads
    [r.id], [r.trk.Progress] and [r.raftLog], so it is stated against the
    raft struct rather than against three unrelated parameters.

    **In scope and unfinished** (2026-09-16).  The generated body
    ([new/code/go_etcd_io/raft/v3.v:5146]) is

        pr := r.trk.Progress[r.id]
        return pr != nil && !pr.IsLearner &&
               !r.raftLog.hasNextOrInProgressSnapshot()

    There were *two* obstacles, and **both are now cleared** -- so this is the
    cheapest remaining win on the election path (STATUS.md, next step 1):

    - [hasNextOrInProgressSnapshot] needs [own_raftLog] opened up.  Since
      2026-09-16 [own_raftLog] is a real **definition** ([inv_raftlog.v])
      carrying [unstable.snapshot = nil], and
      [wp_raftLog__hasNextOrInProgressSnapshot] exists again and is [Qed] --
      it is a postulate of this collection, so the proof reaches it as
      [P.wp_raftLog__hasNextOrInProgressSnapshot].
    - [own_progress] ([inv_tracker.v]) did not record
      [pv.(tracker.Progress.IsLearner') = false], and without it the
      postcondition as stated is **not derivable**: a voter whose [Progress]
      had [IsLearner = true] would make [promotable] return [false] while
      [id ∈ cfg].  That conjunct was added on 2026-09-16 and is now
      [Hnolearner] in [own_progress].

    The statement is correct as written; do not weaken it.  What is left is
    the walk itself: the [r.trk.Progress[r.id]] lookup (see
    [wp_tracker_progress_lookup], [inv_tracker.v]), the two field reads, and
    the call. *)
Definition wp_raft__promotable_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) rv votes,
  {{{ is_pkg_init raft ∗ r ↦ rv ∗
      own_tracker cfg rv.(raft.raft.trk') votes ∗
      own_raftLog rv.(raft.raft.raftLog') }}}
    r @! (go.PointerType raft.raft) @! "promotable" #()
  {{{ (b : bool), RET #b;
      r ↦ rv ∗ own_tracker cfg rv.(raft.raft.trk') votes ∗
      own_raftLog rv.(raft.raft.raftLog') ∗
      ⌜ b = bool_decide (rv.(raft.raft.id') ∈ cfg) ⌝ }}}.

Module Type RAFT__PROMOTABLE.
  Parameter wp_raft__promotable : wp_raft__promotable_body.
  Arguments wp_raft__promotable {_ _ _ _ _ _ _ _}.
End RAFT__PROMOTABLE.
