Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [traceSendMessage(r, m)]: a tracing hook, and a **no-op** -- Goose
    translates it to [λ: <> <>, exception_do (do: #())].  See
    [spec_traceReceiveMessage.v]; [send] is the caller. *)
Definition wp_traceSendMessage_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (r : loc) (mp : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceSendMessage #r #mp
  {{{ RET #(); own_raft_misc rs ro pri }}}.

Module Type TRACESENDMESSAGE.
  Parameter wp_traceSendMessage : wp_traceSendMessage_body.
  Arguments wp_traceSendMessage {_ _ _ _ _ _ _ _}.
End TRACESENDMESSAGE.
