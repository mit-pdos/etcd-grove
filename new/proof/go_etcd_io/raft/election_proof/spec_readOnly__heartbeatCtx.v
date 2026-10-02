Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [ro.heartbeatCtx()] ([readOnly__heartbeatCtxⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:6329; [read_only.go:93]):

      if len(ro.unconfirmedReads) == 0 { return nil }
      ... encode confirmedReads + len(unconfirmedReads) ...

    Under the phase-1 scope there are no read-index requests, and
    [own_read_only] says so ([unconfirmedReads ↦* []], [inv_misc.v]), so
    only the first exit is reachable: the context [bcastHeartbeat] attaches
    to its heartbeats is [nil].  The receiver is a pointer and the body
    reads [ro.unconfirmedReads] through it, so the spec owns the object. *)
Definition wp_readOnly__heartbeatCtx_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (ro : loc),
  {{{ is_pkg_init raft ∗ "Hown" ∷ own_read_only ro }}}
    ro @! (go.PointerType raft.readOnly) @! "heartbeatCtx" #()
  {{{ RET #slice.nil; own_read_only ro }}}.

Module Type READONLY__HEARTBEATCTX.
  Parameter wp_readOnly__heartbeatCtx : wp_readOnly__heartbeatCtx_body.
  Arguments wp_readOnly__heartbeatCtx {_ _ _ _ _ _ _ _}.
End READONLY__HEARTBEATCTX.
