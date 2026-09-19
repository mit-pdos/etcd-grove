Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [l.isUpToDate(e)]: whether the candidate's last entry [e] is at least as
    up to date as ours, which is the log half of the [MsgVote] check.

    The returned boolean is **not** specified, only that the call returns and
    hands the log back.  That is all the election path needs: answering
    [false] when it could have answered [true] makes the node decline to
    vote, which is always protocol-legal, and answering [true] is only
    reachable when the log comparison in [lastEntryID] genuinely holds.
    Specifying it would mean relating the entry lists, which the election
    model does not mention. *)
Definition wp_raftLog__isUpToDate_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (e : raft.entryID.t),
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "isUpToDate" #e
  {{{ (b : bool), RET #b; own_raftLog l }}}.

Module Type RAFTLOG__ISUPTODATE.
  Parameter wp_raftLog__isUpToDate : wp_raftLog__isUpToDate_body.
  Arguments wp_raftLog__isUpToDate {_ _ _ _ _ _ _ _}.
End RAFTLOG__ISUPTODATE.
