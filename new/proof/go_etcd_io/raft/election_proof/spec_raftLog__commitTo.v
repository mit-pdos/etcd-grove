Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** [l.commitTo(tocommit)]: raise [committed] to [tocommit], never lower
    it -- [plog_commit_to] ([plog.v]).

    The body ([raftLog__commitToⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:930):

        if l.committed < tocommit {
            if l.lastIndex() < tocommit { l.logger.Panicf(...) }
            l.committed = tocommit
        }

    The premise [tocommit <= lastIndex()] is exactly what makes the
    [Panicf] dead; it is the protocol fact of the design's table
    ("Protocol facts the code needs": a leader's commit index in an
    accepted [MsgApp]/[MsgHeartbeat] is within the follower's log), and
    for [maybeCommit] it follows from [matchTerm].  It also keeps
    [own_raftLog]'s [Hcommitted] true at the new value. *)
Definition wp_raftLog__commitTo_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (tocommit : w64),
  (uint.Z tocommit ≤ plog_last_index_Z ls.(logstate.prev)
                       (ls.(logstate.sents) ++ ls.(logstate.uents)))%Z →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "commitTo" #tocommit
  {{{ RET #();
      own_raftLog l (ls <| logstate.committed :=
                       plog_commit_to ls.(logstate.committed) tocommit |>) }}}.

Module Type RAFTLOG__COMMITTO.
  Parameter wp_raftLog__commitTo : wp_raftLog__commitTo_body.
  Arguments wp_raftLog__commitTo {_ _ _ _ _ _ _ _}.
End RAFTLOG__COMMITTO.
