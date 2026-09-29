Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [l.scan(lo, hi, pageSize, v)]: page through the entries at [[lo, hi)],
    handing each page to [v]; [nil] unless a page is empty or [v] errs
    ([log.go]).

    The callback is described by [scan_closure f I P] ([inv_raftlog.v]): it
    gets each page (read-only), with [I] and the fact that every entry on the page
    satisfies [P] -- which follows from [Forall P (sents ++ uents)], the
    premise, because every page is a sub-list of the log -- and must return
    [nil].  With that, the "got 0 entries" error is dead ([slice] returns a
    non-empty page on [lo < hi]) and so is the propagated callback error,
    whence [RET #interface.nil].

    [lo <= hi] rather than [lo < hi]: with [lo = hi] the loop does not run
    and the result is [nil] at once, and [hasUnappliedConfChanges] only
    knows [applied + 1 <= committed + 1]. *)
Definition wp_raftLog__scan_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (lo hi pageSize : w64) (f : func.t)
      (I : iProp Σ) (P : raftpb.Entry.t → Prop),
  (uint.Z ls.(logstate.prev).(raft.entryID.index') + 1 ≤ uint.Z lo ≤ uint.Z hi ≤
   uint.Z ls.(logstate.prev).(raft.entryID.index') + Z.of_nat (length ls.(logstate.sents))
   + Z.of_nat (length ls.(logstate.uents)) + 1)%Z →
  Forall P (ls.(logstate.sents) ++ ls.(logstate.uents)) →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls ∗
      "HI" ∷ I ∗ "#Hf" ∷ □ scan_closure f I P }}}
    l @! (go.PointerType raft.raftLog) @! "scan" #lo #hi #pageSize #f
  {{{ RET #interface.nil; own_raftLog l ls ∗ I }}}.

Module Type RAFTLOG__SCAN.
  Parameter wp_raftLog__scan : wp_raftLog__scan_body.
  Arguments wp_raftLog__scan {_ _ _ _ _ _ _ _}.
End RAFTLOG__SCAN.
