Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** The broadcast a new leader sends.  [bcastAppend] visits every peer's
    [Progress] and calls [sendAppend], which reaches [maybeSendAppend] -- and
    that sends a [MsgApp] only when the log and the peer's [Progress] permit
    it, otherwise a [MsgSnap] or nothing at all (the peer is paused, or there
    is nothing to send and [sendIfEmpty] is false).

    So this says **not** one [MsgApp] per peer, only that the outbox grew by
    some list of [App]s from [id] at the current term.  That is exactly what
    the weakened [step_win] asks for, and all the election model ever uses: a
    receiver reads an [App] through [step_higher_term], which cares about its
    term and that a leader sent it.  An earlier version of the model demanded
    one per peer, which would have made this claim false -- the same trap
    [wp_raft__appendEntry] fell into before 2026-09-15 (it was called
    [wp_raft__appendEmptyEntry] then, after a Go method that does not exist). *)
Definition wp_raft__bcastAppend_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) id s,
  s.(nstate.lent) = None →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "bcastAppend" #()
  {{{ (ms : list msg.t), RET #();
      own_raft_phys cfg r id (send_msgs s ms) ∗
      ⌜ app_sends id s.(nstate.term) ms ⌝ }}}.

Module Type RAFT__BCASTAPPEND.
  Parameter wp_raft__bcastAppend : wp_raft__bcastAppend_body.
  Arguments wp_raft__bcastAppend {_ _ _ _ _ _ _ _}.
End RAFT__BCASTAPPEND.
