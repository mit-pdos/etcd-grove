Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [traceReceiveMessage(r, m)]: a tracing hook, and a **no-op**.

    Goose translates it to [λ: <> <>, exception_do (do: #())], so this is a
    two-line proof and not an assumption; it was an axiom until 2026-09-16
    purely because nobody had looked at the generated body.  The spec carries
    [own_raft_misc] in and out so that the call composes where [Step] makes
    it, without claiming anything about the rest of the struct.

    **It owns nothing** (changed 2026-09-23).  Goose translates the hook to
    [exception_do (do: #())]: it reads nothing and writes nothing, so the
    honest triple takes no resource and gives none back.  Until then it
    carried a piece of the raft struct in and out ([own_raft_misc]), which
    was a spec on a raw piece of the struct -- exactly what the
    one-predicate rule (notes/decisions.md, "Three layers") rules out -- and
    was left that way only to spare the callers a re-seal.  Owning nothing
    spares them the re-seal *and* obeys the rule.  This is a fact about the
    no-op build that is translated; the tracing build reads [r] and would
    need a real spec on [own_raft_phys]. *)
Definition wp_traceReceiveMessage_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (r : loc) (mp : loc),
  {{{ is_pkg_init raft }}}
    @! raft.traceReceiveMessage #r #mp
  {{{ RET #(); True }}}.

Module Type TRACERECEIVEMESSAGE.
  Parameter wp_traceReceiveMessage : wp_traceReceiveMessage_body.
  Arguments wp_traceReceiveMessage {_ _ _ _ _ _ _ _}.
End TRACERECEIVEMESSAGE.
