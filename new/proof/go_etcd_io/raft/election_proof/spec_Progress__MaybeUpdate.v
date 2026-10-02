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
    [w64_max] ([defs.v], Goose's [max] verbatim).  [Inflights] is untouched.

    [progress_maybe_update p n] ([defs.v]) is the new record; it is [p]
    itself when the ack is stale.  [matched] becomes [n] exactly when it
    grows. *)
Definition wp_Progress__MaybeUpdate_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (p : progress.t) (n : w64),
  {{{ is_pkg_init tracker ∗ "Hpr" ∷ own_Progress pr p }}}
    pr @! (go.PointerType tracker.Progress) @! "MaybeUpdate" #n
  {{{ RET #(bool_decide (uint.Z p.(progress.matched) < uint.Z n));
      own_Progress pr (progress_maybe_update p n) }}}.

Module Type PROGRESS__MAYBEUPDATE.
  Parameter wp_Progress__MaybeUpdate : wp_Progress__MaybeUpdate_body.
  Arguments wp_Progress__MaybeUpdate {_ _ _ _ _ _ _ _}.
End PROGRESS__MAYBEUPDATE.
