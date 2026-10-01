Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** [l.isUpToDate(e)]: whether the candidate's last entry [e] is at least as
    up to date as ours, which is the log half of the [MsgVote] check:
    [plog_up_to_date] ([plog.v]) of the log the protocol sees.

    Pinned since 2026-10-01 (before, only "returns and hands the log back"):
    with a log in the protocol model, granting a vote records that this
    check passed ([step_grant_vote]'s premise), which leader completeness
    depends on.  The body ([raftLog__isUpToDateⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:1149) is [lastEntryID()] and a
    short-circuit comparison, so this is [lastEntryID]'s widened spec plus
    the two [bool] connectives. *)
Definition wp_raftLog__isUpToDate_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (e : raft.entryID.t) (ls : logstate.t),
  {{{ is_pkg_init raft ∗ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "isUpToDate" #e
  {{{ (b : bool), RET #b; own_raftLog l ls ∗
      ⌜ b = plog_up_to_date ls.(logstate.prev) (ls.(logstate.sents) ++ ls.(logstate.uents)) e ⌝ }}}.

Module Type RAFTLOG__ISUPTODATE.
  Parameter wp_raftLog__isUpToDate : wp_raftLog__isUpToDate_body.
  Arguments wp_raftLog__isUpToDate {_ _ _ _ _ _ _ _}.
End RAFTLOG__ISUPTODATE.
