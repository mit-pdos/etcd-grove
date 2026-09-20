Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [r.sendAppend(to)] is [r.maybeSendAppend(to, true)] and nothing else
    ([raft__sendAppendⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:3076) -- the
    boolean result is dropped.  Same postcondition, therefore: the outbox
    grows by some list of [App]s from [id] at the current term. *)
Definition wp_raft__sendAppend_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t) (to : w64),
  to ≠ id →
  to ∈ cfg →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "sendAppend" #to
  {{{ (ms : list msg.t), RET #();
      own_raft_phys cfg r id (send_msgs s ms) ∗
      ⌜ app_sends id s.(nstate.term) ms ⌝ }}}.

Module Type RAFT__SENDAPPEND.
  Parameter wp_raft__sendAppend : wp_raft__sendAppend_body.
  Arguments wp_raft__sendAppend {_ _ _ _ _ _ _ _}.
End RAFT__SENDAPPEND.
