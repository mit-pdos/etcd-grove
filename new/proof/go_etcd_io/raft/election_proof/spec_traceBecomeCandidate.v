Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [traceBecomeCandidate(r)]: a tracing hook, and a **no-op** -- Goose
    translates it to [λ: <> <>, exception_do (do: #())].  See
    [spec_traceReceiveMessage.v]; [becomeCandidate] is the caller. *)
Definition wp_traceBecomeCandidate_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (r : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeCandidate #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.

Module Type TRACEBECOMECANDIDATE.
  Parameter wp_traceBecomeCandidate : wp_traceBecomeCandidate_body.
  Arguments wp_traceBecomeCandidate {_ _ _ _ _ _ _ _}.
End TRACEBECOMECANDIDATE.
