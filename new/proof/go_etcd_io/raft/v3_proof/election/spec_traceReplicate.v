Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [traceReplicate(r, es...)]: a tracing hook, and a **no-op** -- Goose
    translates it to [λ: <> <>, exception_do (do: #())]
    ([new/code/go_etcd_io/raft/v3.v:6364]).  Same shape as
    [spec_traceSendMessage.v]; [appendEntry] is the caller, and it hands the
    entry slice over only so that the triple has a resource to thread (the
    body touches nothing).

    **It owns nothing** (changed 2026-09-23).  Goose translates the hook to
    [exception_do (do: #())]: it reads nothing and writes nothing, so the
    honest triple takes no resource and gives none back.  Until then it
    carried the entries slice in and out, which it never touches; the other
    five hooks carried a raw piece of the raft struct ([own_raft_misc]),
    and all six now own nothing (notes/decisions.md, "Three layers").  This is a fact about the
    no-op build that is translated; the tracing build reads [r] and would
    need a real spec on [own_raft_phys]. *)
Definition wp_traceReplicate_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (r : loc) (es : slice.t),
  {{{ is_pkg_init raft }}}
    @! raft.traceReplicate #r #es
  {{{ RET #(); True }}}.

Module Type TRACEREPLICATE.
  Parameter wp_traceReplicate : wp_traceReplicate_body.
  Arguments wp_traceReplicate {_ _ _ _ _ _ _ _}.
End TRACEREPLICATE.
