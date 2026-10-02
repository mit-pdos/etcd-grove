Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [p.VoterNodes()] is the voter ids, sorted.  As for [MajorityConfig.Slice],
    only the permutation is stated.  [newRaft] uses it only to build a log
    line. *)
Definition wp_ProgressTracker__VoterNodes_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (trk : loc) tv (t : trk.t),
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker cfg tv t }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "VoterNodes" #()
  {{{ (sl : slice.t) (xs : list w64), RET #sl;
      trk ↦ tv ∗ own_tracker cfg tv t ∗
      sl ↦* xs ∗ ⌜ xs ≡ₚ elements cfg ⌝ }}}.

Module Type PROGRESSTRACKER__VOTERNODES.
  Parameter wp_ProgressTracker__VoterNodes : wp_ProgressTracker__VoterNodes_body.
  Arguments wp_ProgressTracker__VoterNodes {_ _ _ _ _ _ _ _}.
End PROGRESSTRACKER__VOTERNODES.
