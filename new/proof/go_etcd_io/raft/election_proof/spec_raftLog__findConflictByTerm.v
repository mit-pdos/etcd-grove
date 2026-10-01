Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** [l.findConflictByTerm(index, term)]: a guess [(i', t')] at where our
    log stops agreeing with a log whose entry at [index] has term [term].

    Only [i' <= index] is specified, and the log is unchanged.  The result
    is a *hint* -- the [RejectHint]/[LogTerm] of a rejecting [MsgAppResp],
    and the leader's next probe -- and the protocol model takes any hint
    ([step_app_reject] quantifies over it), so pinning it buys nothing for
    safety.

    The body ([raftLog__findConflictByTermⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:681) is

        for ; index > 0; index-- {
            if ourTerm, err := l.term(index); err != nil { return index, 0 }
            else if ourTerm <= term { return index, ourTerm }
        }
        return 0, 0

    with no panic; the loop invariant is that the counter has only gone
    down.  [term] is total, so no premise is needed. *)
Definition wp_raftLog__findConflictByTerm_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (index term : w64),
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "findConflictByTerm" #index #term
  {{{ (i' t' : w64), RET (#i', #t');
      own_raftLog l ls ∗ ⌜ (uint.Z i' ≤ uint.Z index)%Z ⌝ }}}.

Module Type RAFTLOG__FINDCONFLICTBYTERM.
  Parameter wp_raftLog__findConflictByTerm : wp_raftLog__findConflictByTerm_body.
  Arguments wp_raftLog__findConflictByTerm {_ _ _ _ _ _ _ _}.
End RAFTLOG__FINDCONFLICTBYTERM.
