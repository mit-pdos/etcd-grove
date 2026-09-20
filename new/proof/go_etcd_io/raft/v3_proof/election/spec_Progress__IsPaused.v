Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [pr.IsPaused()] -- "should the leader hold off sending log entries to this
    peer".  The body ([Progress__IsPausedⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3/tracker.v:443) switches on [pr.State]:

      StateProbe, StateReplicate -> pr.MsgAppFlowPaused
      StateSnapshot              -> true
      anything else              -> panic("unexpected state")

    The fourth arm is why [own_progress] carries [progress_state_ok]
    ([inv_tracker.v]): [bcastAppend] reaches [IsPaused] on every peer, so the
    panic has to be ruled out by an invariant rather than by inspection.

    Stated at a fixed [Progress] value ([own_progress_at]) because the answer
    *is* a function of that value, and [maybeSendAppend] needs to know which
    branch it took: a [false] answer tells it [State ≠ StateSnapshot], which
    is what makes the later [SentEntries] call legal (that one panics in
    [StateSnapshot]). *)
Definition progress_paused (pv : tracker.Progress.t) : bool :=
  if decide (pv.(tracker.Progress.State') = W64 2) then true
  else pv.(tracker.Progress.MsgAppFlowPaused').

Definition wp_Progress__IsPaused_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (pv : tracker.Progress.t) (iv : tracker.Inflights.t),
  {{{ is_pkg_init tracker ∗ "Hpr" ∷ own_progress_at pr pv iv }}}
    pr @! (go.PointerType tracker.Progress) @! "IsPaused" #()
  {{{ RET #(progress_paused pv); own_progress_at pr pv iv }}}.

Module Type PROGRESS__ISPAUSED.
  Parameter wp_Progress__IsPaused : wp_Progress__IsPaused_body.
  Arguments wp_Progress__IsPaused {_ _ _ _ _ _ _ _}.
End PROGRESS__ISPAUSED.
