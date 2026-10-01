Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [pr.MaybeUpdate(n)] records that the peer has acknowledged index [n]
    ([Progress__MaybeUpdateⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:370;
    progress.go:205):

        if n <= pr.Match { return false }          // exit 1: stale ack
        pr.Match = n
        pr.Next = max(pr.Next, n+1)
        pr.MsgAppFlowPaused = false
        return true                                // exit 2

    No panic, no call ([max] is the builtin).  [n+1] is [uint64]
    arithmetic and wraps at [n = 2^64-1], where Go's [max] then keeps
    [pr.Next]; the postcondition says exactly that, with [word.add] and
    [w64_max] ([inv_tracker.v], Goose's [max] verbatim).  [Inflights] is untouched.

    [progress_maybe_update pv n] is the new value; it is [pv] itself when
    the ack is stale.  [Match] becomes [n] exactly when it grows. *)
Definition progress_maybe_update (pv : tracker.Progress.t) (n : w64) : tracker.Progress.t :=
  if bool_decide (uint.Z pv.(tracker.Progress.Match') < uint.Z n) then
    pv <| tracker.Progress.Match' := n |>
       <| tracker.Progress.Next' := w64_max pv.(tracker.Progress.Next') (word.add n (W64 1)) |>
       <| tracker.Progress.MsgAppFlowPaused' := false |>
  else pv.

Definition wp_Progress__MaybeUpdate_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (pv : tracker.Progress.t) (iv : tracker.Inflights.t)
    (n : w64),
  {{{ is_pkg_init tracker ∗ "Hpr" ∷ own_progress pr pv iv }}}
    pr @! (go.PointerType tracker.Progress) @! "MaybeUpdate" #n
  {{{ RET #(bool_decide (uint.Z pv.(tracker.Progress.Match') < uint.Z n));
      own_progress pr (progress_maybe_update pv n) iv }}}.

Module Type PROGRESS__MAYBEUPDATE.
  Parameter wp_Progress__MaybeUpdate : wp_Progress__MaybeUpdate_body.
  Arguments wp_Progress__MaybeUpdate {_ _ _ _ _ _ _ _}.
End PROGRESS__MAYBEUPDATE.
