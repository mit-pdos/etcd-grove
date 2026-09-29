Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [r.promotable()]: true exactly when this node is a voter.  It reads
    [r.id], [r.trk.Progress] and [r.raftLog], so it is stated against the
    raft struct rather than against three unrelated parameters.

    **Proved** ([proof_raft__promotable.v], [Qed] 2026-09-19).  The generated
    body ([new/code/go_etcd_io/raft/v3.v:5146]) is

        pr := r.trk.Progress[r.id]
        return pr != nil && !pr.IsLearner &&
               !r.raftLog.hasNextOrInProgressSnapshot()

    There were *two* obstacles to stating it this way, both cleared on
    2026-09-16 and recorded here because the statement depends on them:

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

    The statement is correct as written; do not weaken it.  The proof is a
    case split on [id ∈ cfg]: present, the [r.trk.Progress[r.id]] lookup
    (see [wp_tracker_progress_lookup], [inv_tracker.v]) yields a non-nil,
    non-learner [Progress] and the call returns [false]; absent, the lookup
    yields [nil] and the [&&] short-circuits. *)
Definition wp_raft__promotable_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t),
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "promotable" #()
  {{{ (b : bool), RET #b;
      own_raft_phys cfg r id s ∗ ⌜ b = bool_decide (id ∈ cfg) ⌝ }}}.

Module Type RAFT__PROMOTABLE.
  Parameter wp_raft__promotable : wp_raft__promotable_body.
  Arguments wp_raft__promotable {_ _ _ _ _ _ _ _}.
End RAFT__PROMOTABLE.
