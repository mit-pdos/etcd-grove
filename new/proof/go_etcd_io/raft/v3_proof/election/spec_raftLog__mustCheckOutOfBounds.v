Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [l.mustCheckOutOfBounds(lo, hi)]: [nil] when
    [firstIndex <= lo <= hi <= lastIndex + 1].

    Stated at a fixed split ([_at]) because it calls [firstIndex] and
    [lastIndex] on the log, whose specs are.  The two [Panicf]s ([lo > hi],
    and [hi] past the end) and the [ErrCompacted] return ([lo < firstIndex])
    are all excluded by the range premise, so the result is exactly [nil] --
    which is what lets [raftLog.slice] take its non-error path. *)
Definition wp_raftLog__mustCheckOutOfBounds_at_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) prev sents uents (lo hi : w64),
  (uint.Z prev.(raft.entryID.index') + 1 ≤ uint.Z lo ≤ uint.Z hi ≤
   uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
   + Z.of_nat (length uents) + 1)%Z →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog_at l prev sents uents }}}
    l @! (go.PointerType raft.raftLog) @! "mustCheckOutOfBounds" #lo #hi
  {{{ RET #interface.nil; own_raftLog_at l prev sents uents }}}.

Module Type RAFTLOG__MUSTCHECKOUTOFBOUNDS.
  Parameter wp_raftLog__mustCheckOutOfBounds_at : wp_raftLog__mustCheckOutOfBounds_at_body.
  Arguments wp_raftLog__mustCheckOutOfBounds_at {_ _ _ _ _ _ _ _}.
End RAFTLOG__MUSTCHECKOUTOFBOUNDS.
