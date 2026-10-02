Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [pr.ResetState(st)] resets the [Progress] to state [st] and empties its
    [Inflights] (whence the [Inflights.reset] postulate):

      pr.MsgAppFlowPaused = false
      pr.PendingSnapshot = 0
      pr.State = state
      pr.Inflights.reset()

    Stated on [own_Progress] at the exact new record,
    [progress_reset_state p st] ([defs.v]).  The argument is a [prstate.t]
    passed as its [StateType] ([prstate_w64]), so no other value can be
    passed -- what the premise [progress_state_ok st] said until
    2026-10-02.  (Until 2026-09-23 it was stated on the raw field
    points-tos.) *)
Definition wp_Progress__ResetState_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (p : progress.t) (st : prstate.t),
  {{{ is_pkg_init tracker ∗ own_Progress pr p }}}
    pr @! (go.PointerType tracker.Progress) @! "ResetState" #(prstate_w64 st)
  {{{ RET #(); own_Progress pr (progress_reset_state p st) }}}.

Module Type PROGRESS__RESETSTATE.
  Parameter wp_Progress__ResetState : wp_Progress__ResetState_body.
  Arguments wp_Progress__ResetState {_ _ _ _ _ _ _ _}.
End PROGRESS__RESETSTATE.
