Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [pr.CanBumpCommit(index)] is a pure test on the [Progress]
    ([Progress__CanBumpCommitⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:348;
    progress.go:189):

        return index > pr.sentCommit && pr.sentCommit < pr.Next-1

    One exit, no panic, no call, no write.  [pr.Next-1] is [uint64]
    arithmetic and wraps to [2^64-1] at [Next = 0] (the body does not
    guard it; [own_Progress] does not bound [Next]), so the subtraction is
    [word.sub] in [progress_can_bump_commit] ([defs.v]). *)
Definition wp_Progress__CanBumpCommit_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (p : progress.t) (index : w64),
  {{{ is_pkg_init tracker ∗ "Hpr" ∷ own_Progress pr p }}}
    pr @! (go.PointerType tracker.Progress) @! "CanBumpCommit" #index
  {{{ RET #(progress_can_bump_commit p index); own_Progress pr p }}}.

Module Type PROGRESS__CANBUMPCOMMIT.
  Parameter wp_Progress__CanBumpCommit : wp_Progress__CanBumpCommit_body.
  Arguments wp_Progress__CanBumpCommit {_ _ _ _ _ _ _ _}.
End PROGRESS__CANBUMPCOMMIT.
