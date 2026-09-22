Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [traceReplicate(r, es...)]: a tracing hook, and a **no-op** -- Goose
    translates it to [λ: <> <>, exception_do (do: #())]
    ([new/code/go_etcd_io/raft/v3.v:6364]).  Same shape as
    [spec_traceSendMessage.v]; [appendEntry] is the caller, and it hands the
    entry slice over only so that the triple has a resource to thread (the
    body touches nothing). *)
Definition wp_traceReplicate_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (r : loc) (es : slice.t) (ents : list raftpb.Entry.t) (dq : dfrac),
  {{{ is_pkg_init raft ∗ "Hes" ∷ es ↦*{dq} ents }}}
    @! raft.traceReplicate #r #es
  {{{ RET #(); es ↦*{dq} ents }}}.

Module Type TRACEREPLICATE.
  Parameter wp_traceReplicate : wp_traceReplicate_body.
  Arguments wp_traceReplicate {_ _ _ _ _ _ _ _}.
End TRACEREPLICATE.
