Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [switchToConfig]'s tracing hook.  A no-op in the translated build
    ([state_trace_nop.go]); it owns nothing. *)
Definition wp_traceConfChangeEvent_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (c : tracker.Config.t) (r : loc),
  {{{ is_pkg_init raft }}}
    @! raft.traceConfChangeEvent #c #r
  {{{ RET #(); True }}}.

Module Type TRACECONFCHANGEEVENT.
  Parameter wp_traceConfChangeEvent : wp_traceConfChangeEvent_body.
  Arguments wp_traceConfChangeEvent {_ _ _ _ _ _ _ _}.
End TRACECONFCHANGEEVENT.
