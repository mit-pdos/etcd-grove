Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** Out of scope: the empty entry a new leader appends.  [appendEntry]
    updates the log and then queues a self-addressed [MsgAppResp]
    ([new/code/go_etcd_io/raft/v3.v], the [send] at the end of
    [raft__appendEntryⁱᵐᵖˡ]).  [mtype_of MsgAppResp = None], so [abs_msg_opt]
    drops it and the abstract state — outbox included — is unchanged.

    It is discharged by an [Axiom] inside [proof_raft__appendEntry.v]'s
    functor, which is how a trust-boundary triple is carried here — the
    keyword still makes it an assumption under [Print Assumptions].

    Two pieces of history, because this claim has been wrong before.  Its
    form before 2026-09-15 owned only [own_raftLog] while the code it
    describes writes [r.msgsAfterAppend], which made it **false**; it could
    not be stated honestly before the outbox was abstracted, because the old
    [is_phys_msg] clause was unprovable for a [MsgAppResp].  And until
    2026-09-18 it was called [wp_raft__appendEmptyEntry], after a Go method
    that **does not exist** — the method is [appendEntry].  Both are in
    notes/false-statements.md. *)
Definition wp_raft__appendEntry_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64),
  ∀ (r : loc) id s (es : slice.t),
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "appendEntry" #es
  {{{ RET #true; own_raft_phys cfg r id s }}}.

Module Type RAFT__APPENDENTRY.
  Parameter wp_raft__appendEntry : wp_raft__appendEntry_body.
  Arguments wp_raft__appendEntry {_ _ _ _ _ _ _ _}.
End RAFT__APPENDENTRY.
