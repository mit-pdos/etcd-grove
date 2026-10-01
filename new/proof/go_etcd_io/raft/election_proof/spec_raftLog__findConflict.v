Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.plog.

(** [l.findConflict(ents)]: the index of the first entry of the batch the
    log does not have (a different term at that index, or nothing there);
    [0] if it has them all -- [plog_find_conflict] ([plog.v]).

    The body ([raftLog__findConflictⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:634):

        for i := range ents {
            if id := pbEntryID(&ents[i]); !l.matchTerm(id) {
                if id.index <= l.lastIndex() {
                    l.logger.Infof("found conflict ...", id.index,
                        l.zeroTermOnOutOfBounds(l.term(id.index)), id.term)
                }
                return id.index
            }
        }
        return 0

    **Premise**: every entry of the batch is at or above the compaction
    boundary [prev.index].  It is not about the result (which is
    [plog_find_conflict] regardless) but about the log line: at a
    conflicting entry with [id.index <= lastIndex()] it makes [term] return
    a [nil] error, which is what [zeroTermOnOutOfBounds]'s spec takes
    (see there for why that spec stops at [nil]).  [maybeAppend] supplies
    it: its batch starts right after [a.prev], which [matchTerm] has just
    placed at or above [prev.index].  The Go comment's "the index of the
    given entries MUST be continuously increasing" is not needed for this
    function -- [plog_find_conflict] is defined entry by entry, as the loop
    is.

    The batch is lent at any fraction and comes back; the log is
    unchanged. *)
Definition wp_raftLog__findConflict_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (es : slice.t) (dq : dfrac) (ents : list raftpb.Entry.t),
  Forall (λ e, uint.Z ls.(logstate.prev).(raft.entryID.index') ≤ uint.Z e.(raftpb.Entry.Index'))%Z
    ents →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls ∗ "Hes" ∷ es ↦*{dq} ents }}}
    l @! (go.PointerType raft.raftLog) @! "findConflict" #es
  {{{ RET #(plog_find_conflict ls.(logstate.prev)
              (ls.(logstate.sents) ++ ls.(logstate.uents)) ents);
      own_raftLog l ls ∗ es ↦*{dq} ents }}}.

Module Type RAFTLOG__FINDCONFLICT.
  Parameter wp_raftLog__findConflict : wp_raftLog__findConflict_body.
  Arguments wp_raftLog__findConflict {_ _ _ _ _ _ _ _}.
End RAFTLOG__FINDCONFLICT.
