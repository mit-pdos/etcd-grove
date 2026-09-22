Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [abortLeaderTransfer] clears [leadTransferee], which [own_raft_phys]
    requires to be zero anyway. *)
Definition wp_raft__abortLeaderTransfer_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (r : loc) rv,
  {{{ is_pkg_init raft ∗ r ↦ rv }}}
    r @! (go.PointerType raft.raft) @! "abortLeaderTransfer" #()
  {{{ RET #(); r ↦ (rv <| raft.raft.leadTransferee' := W64 0 |>) }}}.

Module Type RAFT__ABORTLEADERTRANSFER.
  Parameter wp_raft__abortLeaderTransfer : wp_raft__abortLeaderTransfer_body.
  Arguments wp_raft__abortLeaderTransfer {_ _ _ _ _ _ _ _}.
End RAFT__ABORTLEADERTRANSFER.
