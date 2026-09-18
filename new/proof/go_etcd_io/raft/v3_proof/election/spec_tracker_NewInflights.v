Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [NewInflights] allocates one. *)
Definition wp_tracker_NewInflights_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (size maxBytes : w64),
  {{{ is_pkg_init tracker }}}
    @! tracker.NewInflights #size #maxBytes
  {{{ (l : loc), RET #l; own_inflights l }}}.

Module Type TRACKER_NEWINFLIGHTS.
  Parameter wp_tracker_NewInflights : wp_tracker_NewInflights_body.
  Arguments wp_tracker_NewInflights {_ _ _ _ _ _ _ _}.
End TRACKER_NEWINFLIGHTS.
