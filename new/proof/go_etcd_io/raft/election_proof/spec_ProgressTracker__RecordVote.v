Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [RecordVote] only inserts into the map [p.Votes] already refers to, so
    the tracker value is unchanged.  First write wins, which is [record_vote]. *)
Definition wp_ProgressTracker__RecordVote_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (trk : loc) tv votes (prs : gmap w64 loc) (from : w64) (v : bool),
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker cfg tv votes prs }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "RecordVote" #from #v
  {{{ RET #(); trk ↦ tv ∗ own_tracker cfg tv (record_vote votes from v) prs }}}.

Module Type PROGRESSTRACKER__RECORDVOTE.
  Parameter wp_ProgressTracker__RecordVote : wp_ProgressTracker__RecordVote_body.
  Arguments wp_ProgressTracker__RecordVote {_ _ _ _ _ _ _ _}.
End PROGRESSTRACKER__RECORDVOTE.
