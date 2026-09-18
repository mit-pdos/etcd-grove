Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [traceReceiveMessage(r, m)]: a tracing hook, and a **no-op**.

    Goose translates it to [λ: <> <>, exception_do (do: #())], so this is a
    two-line proof and not an assumption; it was an axiom until 2026-09-16
    purely because nobody had looked at the generated body.  The spec carries
    [own_raft_misc] in and out so that the call composes where [Step] makes
    it, without claiming anything about the rest of the struct. *)
Definition wp_traceReceiveMessage_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (r : loc) (mp : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceReceiveMessage #r #mp
  {{{ RET #(); own_raft_misc rs ro pri }}}.

Module Type TRACERECEIVEMESSAGE.
  Parameter wp_traceReceiveMessage : wp_traceReceiveMessage_body.
  Arguments wp_traceReceiveMessage {_ _ _ _ _ _ _ _}.
End TRACERECEIVEMESSAGE.
