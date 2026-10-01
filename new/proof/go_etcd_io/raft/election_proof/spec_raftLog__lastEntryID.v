Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** [l.lastEntryID()]: the id of the last entry, or of the compaction
    boundary [prev] when the log after it is empty -- [plog_last] ([plog.v])
    of the log the protocol sees.

    The body ([raftLog__lastEntryIDⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:1036)
    is [lastIndex()] then [term(lastIndex())], with a [Panicf] on an error
    from [term]; [term]'s iff kills it, and its widened postcondition
    ([plog_term_at … = Some t]) pins the term.  Until 2026-10-01 the result
    was unspecified (only [isUpToDate] read it, and a wrong answer there
    could only make the node decline a vote); log replication needs it:
    the vote rule now checks the candidate's log is up to date
    ([plog_up_to_date]), and [campaign] sends it in [MsgVote]. *)
Definition wp_raftLog__lastEntryID_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t),
  {{{ is_pkg_init raft ∗ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "lastEntryID" #()
  {{{ (e : raft.entryID.t), RET #e; own_raftLog l ls ∗
      ⌜ e = plog_last ls.(logstate.prev) (ls.(logstate.sents) ++ ls.(logstate.uents)) ⌝ }}}.

Module Type RAFTLOG__LASTENTRYID.
  Parameter wp_raftLog__lastEntryID : wp_raftLog__lastEntryID_body.
  Arguments wp_raftLog__lastEntryID {_ _ _ _ _ _ _ _}.
End RAFTLOG__LASTENTRYID.
