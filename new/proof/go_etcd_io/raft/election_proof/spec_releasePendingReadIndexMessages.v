Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [releasePendingReadIndexMessages(r)]
    ([releasePendingReadIndexMessagesⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:5423;
    [raft.go:2115]):

      if len(r.pendingReadIndexMessages) == 0 { return }
      if !r.committedEntryInCurrentTerm() { r.logger.Error(...); return }
      msgs := r.pendingReadIndexMessages
      r.pendingReadIndexMessages = nil
      for _, m := range msgs { sendMsgReadIndexResponse(r, m) }

    Under the phase-1 scope no [MsgReadIndex] is ever pending
    ([own_raft_misc]'s [pendingReadIndexMessages ↦* []], [inv_misc.v]), so
    the first test returns at once and the struct is unchanged.
    [stepLeader] calls it after a successful [maybeCommit]. *)
Definition wp_releasePendingReadIndexMessages_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t),
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
    @! raft.releasePendingReadIndexMessages #r
  {{{ RET #(); own_raft_phys cfg r id s }}}.

Module Type RELEASEPENDINGREADINDEXMESSAGES.
  Parameter wp_releasePendingReadIndexMessages :
    wp_releasePendingReadIndexMessages_body.
  Arguments wp_releasePendingReadIndexMessages {_ _ _ _ _ _ _ _}.
End RELEASEPENDINGREADINDEXMESSAGES.
