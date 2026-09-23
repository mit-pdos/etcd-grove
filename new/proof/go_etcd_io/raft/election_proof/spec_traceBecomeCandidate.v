Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [traceBecomeCandidate(r)]: a tracing hook, and a **no-op** -- Goose
    translates it to [λ: <> <>, exception_do (do: #())].  See
    [spec_traceReceiveMessage.v]; [becomeCandidate] is the caller.

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
Definition wp_traceBecomeCandidate_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (r : loc),
  {{{ is_pkg_init raft }}}
    @! raft.traceBecomeCandidate #r
  {{{ RET #(); True }}}.

Module Type TRACEBECOMECANDIDATE.
  Parameter wp_traceBecomeCandidate : wp_traceBecomeCandidate_body.
  Arguments wp_traceBecomeCandidate {_ _ _ _ _ _ _ _}.
End TRACEBECOMECANDIDATE.
