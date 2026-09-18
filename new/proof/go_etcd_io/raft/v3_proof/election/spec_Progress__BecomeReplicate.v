Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [pr.BecomeReplicate()] moves a [Progress] into the replicating state.
    It says nothing about votes, terms or roles, so the model does not see
    it. *)
Definition wp_Progress__BecomeReplicate_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc),
  {{{ is_pkg_init tracker ∗ own_progress pr }}}
    pr @! (go.PointerType tracker.Progress) @! "BecomeReplicate" #()
  {{{ RET #(); own_progress pr }}}.

Module Type PROGRESS__BECOMEREPLICATE.
  Parameter wp_Progress__BecomeReplicate : wp_Progress__BecomeReplicate_body.
  Arguments wp_Progress__BecomeReplicate {_ _ _ _ _ _ _ _}.
End PROGRESS__BECOMEREPLICATE.
