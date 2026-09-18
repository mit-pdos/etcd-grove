Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** ** The interface other files use

    These four statements are what [inv_raft_phys.v], [inv_misc.v] and the
    [proof_*.v] files call.  The first three are unchanged from when they were
    [Axiom]s: they say nothing about the value returned, only that the call
    returns and gives the log back.  That is all the election path needs --
    [isUpToDate] returning a wrong answer can only make the node decline to
    vote, which is always protocol-legal. *)
Definition wp_raftLog__lastEntryID_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc),
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "lastEntryID" #()
  {{{ (e : raft.entryID.t), RET #e; own_raftLog l }}}.

Module Type RAFTLOG__LASTENTRYID.
  Parameter wp_raftLog__lastEntryID : wp_raftLog__lastEntryID_body.
  Arguments wp_raftLog__lastEntryID {_ _ _ _ _ _ _ _}.
End RAFTLOG__LASTENTRYID.
