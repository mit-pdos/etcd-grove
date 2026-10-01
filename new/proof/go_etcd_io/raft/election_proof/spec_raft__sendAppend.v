Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [r.sendAppend(to)] is [r.maybeSendAppend(to, true)] and nothing else
    ([raft__sendAppendⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:3076) -- the
    boolean result is dropped.  Same postcondition, therefore: the outbox
    grows by some list of messages [repl_ok] allows, and [Match] does not
    move. *)
Definition wp_raft__sendAppend_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t) (to : w64),
  to ≠ id →
  to ∈ cfg →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "sendAppend" #to
  {{{ (ms : list msg.t) pvs, RET #();
      own_raft_phys cfg r id (send_msgs s ms <| nstate.prvals := pvs |>) ∗
      ⌜ repl_sends id s ms ⌝ ∗
      ⌜ prvals_match pvs = prvals_match s.(nstate.prvals) ⌝ }}}.

Module Type RAFT__SENDAPPEND.
  Parameter wp_raft__sendAppend : wp_raft__sendAppend_body.
  Arguments wp_raft__sendAppend {_ _ _ _ _ _ _ _}.
End RAFT__SENDAPPEND.
