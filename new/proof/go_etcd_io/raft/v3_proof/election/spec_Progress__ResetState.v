Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [pr.ResetState(st)] resets the [Progress] to state [st] and empties its
    [Inflights] (whence the [Inflights.reset] postulate).

    Stated over the *field* points-tos rather than over [own_progress] /
    [own_inflights], because the caller's [wp_auto] has to keep stepping
    through field reads after the call returns and cannot see through an
    opaque predicate -- see notes/gotchas.md.  [BecomeReplicate] is the one
    caller. *)
Definition wp_Progress__ResetState_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (pv : tracker.Progress.t)
  (iv : tracker.Inflights.t) (st : tracker.StateType.t),
  {{{ is_pkg_init tracker ∗ pr ↦ pv ∗ pv.(tracker.Progress.Inflights') ↦ iv }}}
    pr @! (go.PointerType tracker.Progress) @! "ResetState" #st
  {{{ RET #();
      pr ↦ (pv <| tracker.Progress.MsgAppFlowPaused' := false |>
               <| tracker.Progress.PendingSnapshot' := W64 0 |>
               <| tracker.Progress.State' := st |>) ∗
      pv.(tracker.Progress.Inflights') ↦ (iv
             <| tracker.Inflights.start' := W64 0 |>
             <| tracker.Inflights.count' := W64 0 |>
             <| tracker.Inflights.bytes' := W64 0 |>) }}}.

Module Type PROGRESS__RESETSTATE.
  Parameter wp_Progress__ResetState : wp_Progress__ResetState_body.
  Arguments wp_Progress__ResetState {_ _ _ _ _ _ _ _}.
End PROGRESS__RESETSTATE.
