Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [ResetVotes] assigns a fresh empty map to [p.Votes], so it changes the
    tracker value as well as the heap it points at. *)
Definition wp_ProgressTracker__ResetVotes_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (trk : loc) tv votes,
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker cfg tv votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "ResetVotes" #()
  {{{ (votesRef : loc), RET #();
      trk ↦ (tv <| tracker.ProgressTracker.Votes' := votesRef |>) ∗
      own_tracker cfg (tv <| tracker.ProgressTracker.Votes' := votesRef |>) ∅ }}}.

Module Type PROGRESSTRACKER__RESETVOTES.
  Parameter wp_ProgressTracker__ResetVotes : wp_ProgressTracker__ResetVotes_body.
  Arguments wp_ProgressTracker__ResetVotes {_ _ _ _ _ _ _ _}.
End PROGRESSTRACKER__RESETVOTES.
