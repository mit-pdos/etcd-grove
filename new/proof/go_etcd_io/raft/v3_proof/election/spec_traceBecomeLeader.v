Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [traceBecomeLeader(r)]: a tracing hook, and a **no-op** -- Goose
    translates it to [λ: <> <>, exception_do (do: #())].  See
    [spec_traceReceiveMessage.v]; [becomeLeader] is the caller. *)
Definition wp_traceBecomeLeader_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (r : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeLeader #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.

Module Type TRACEBECOMELEADER.
  Parameter wp_traceBecomeLeader : wp_traceBecomeLeader_body.
  Arguments wp_traceBecomeLeader {_ _ _ _ _ _ _ _}.
End TRACEBECOMELEADER.
