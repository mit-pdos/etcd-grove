Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [pr.ResetState(st)] resets the [Progress] to state [st] and empties its
    [Inflights] (whence the [Inflights.reset] postulate).  Stated on
    [own_progress] at the exact new values, so a caller that has to keep
    stepping field reads afterwards opens the predicate it gets back.
    (Until 2026-09-23 it was stated on the raw field points-tos, for exactly
    that reason -- the reason is answered by the exact index, not by a
    second shape.)  [progress_state_ok st] is what keeps [own_progress]'s
    own invariant; both callers pass a literal state. *)
Definition wp_Progress__ResetState_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (pv : tracker.Progress.t)
  (iv : tracker.Inflights.t) (st : tracker.StateType.t),
  progress_state_ok st →
  {{{ is_pkg_init tracker ∗ own_progress pr pv iv }}}
    pr @! (go.PointerType tracker.Progress) @! "ResetState" #st
  {{{ RET #();
      own_progress pr
        (pv <| tracker.Progress.MsgAppFlowPaused' := false |>
            <| tracker.Progress.PendingSnapshot' := W64 0 |>
            <| tracker.Progress.State' := st |>)
        (iv <| tracker.Inflights.start' := W64 0 |>
            <| tracker.Inflights.count' := W64 0 |>
            <| tracker.Inflights.bytes' := W64 0 |>) }}}.

Module Type PROGRESS__RESETSTATE.
  Parameter wp_Progress__ResetState : wp_Progress__ResetState_body.
  Arguments wp_Progress__ResetState {_ _ _ _ _ _ _ _}.
End PROGRESS__RESETSTATE.
