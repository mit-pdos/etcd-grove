Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [pr.IsPaused()] -- "should the leader hold off sending log entries to this
    peer".  The body ([Progress__IsPausedⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3/tracker.v:443) switches on [pr.State]:

      StateProbe, StateReplicate -> pr.MsgAppFlowPaused
      StateSnapshot              -> true
      anything else              -> panic("unexpected state")

    The fourth arm is why [own_Progress]'s record has an inductive state
    ([progress_abs], [defs.v]): [bcastAppend] reaches [IsPaused] on every
    peer, so the panic has to be ruled out by an invariant rather than by
    inspection.

    The answer is [progress_is_paused p] ([defs.v]), a function of the
    record, and [maybeSendAppend] needs to know which branch it took: a
    [false] answer tells it [state ≠ Snapshot], which is what makes the
    later [SentEntries] call legal (that one panics in [StateSnapshot]). *)
Definition wp_Progress__IsPaused_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (p : progress.t),
  {{{ is_pkg_init tracker ∗ "Hpr" ∷ own_Progress pr p }}}
    pr @! (go.PointerType tracker.Progress) @! "IsPaused" #()
  {{{ RET #(progress_is_paused p); own_Progress pr p }}}.

Module Type PROGRESS__ISPAUSED.
  Parameter wp_Progress__IsPaused : wp_Progress__IsPaused_body.
  Arguments wp_Progress__IsPaused {_ _ _ _ _ _ _ _}.
End PROGRESS__ISPAUSED.
