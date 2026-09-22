Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [traceBecomeFollower(r)]: a tracing hook, and a **no-op** -- Goose
    translates it to [λ: <> <>, exception_do (do: #())].  See
    [spec_traceReceiveMessage.v]; [becomeFollower] is the caller. *)
Definition wp_traceBecomeFollower_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (r : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeFollower #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.

Module Type TRACEBECOMEFOLLOWER.
  Parameter wp_traceBecomeFollower : wp_traceBecomeFollower_body.
  Arguments wp_traceBecomeFollower {_ _ _ _ _ _ _ _}.
End TRACEBECOMEFOLLOWER.
