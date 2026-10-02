Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [traceCommit(r)]: a tracing hook, and a **no-op** -- Goose translates
    it to [λ: <>, exception_do (do: #())] ([traceCommitⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:6359).  Same shape as the other trace
    hooks ([spec_traceBecomeLeader.v]): it owns nothing.  [maybeCommit]
    calls it through a [defer]. *)
Definition wp_traceCommit_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (r : loc),
  {{{ is_pkg_init raft }}}
    @! raft.traceCommit #r
  {{{ RET #(); True }}}.

Module Type TRACECOMMIT.
  Parameter wp_traceCommit : wp_traceCommit_body.
  Arguments wp_traceCommit {_ _ _ _ _ _ _ _}.
End TRACECOMMIT.
