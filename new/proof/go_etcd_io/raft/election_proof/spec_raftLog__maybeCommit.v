Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** [l.maybeCommit(at)]: commit up to [at.index] if [at] is a non-zero-term
    entry of our log past the commit index.

    The body ([raftLog__maybeCommitⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:1177):

        if at.term != 0 && at.index > l.committed && l.matchTerm(at) {
            l.commitTo(at.index); return true
        }
        return false

    The result [b] is exactly the guard, and the log moves to
    [committed := at.index] when it is [true].  [commitTo]'s premise
    ([at.index <= lastIndex()]) is not a premise here: [matchTerm] put
    [at.index] inside the log ([plog_term_at_Some_range]), so its [Panicf] is
    dead with no help from the caller.  The leader's [raft.maybeCommit]
    calls this with [at = (trk.Committed(), r.Term)]. *)
Definition wp_raftLog__maybeCommit_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (aid : raft.entryID.t),
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "maybeCommit" #aid
  {{{ (b : bool), RET #b;
      own_raftLog l (if b then ls <| logstate.committed := aid.(raft.entryID.index') |>
                     else ls) ∗
      ⌜ b = bool_decide (aid.(raft.entryID.term') ≠ W64 0 ∧
                         uint.Z ls.(logstate.committed) < uint.Z aid.(raft.entryID.index') ∧
                         plog_matches ls.(logstate.prev)
                           (ls.(logstate.sents) ++ ls.(logstate.uents)) aid) ⌝ }}}.

Module Type RAFTLOG__MAYBECOMMIT.
  Parameter wp_raftLog__maybeCommit : wp_raftLog__maybeCommit_body.
  Arguments wp_raftLog__maybeCommit {_ _ _ _ _ _ _ _}.
End RAFTLOG__MAYBECOMMIT.
