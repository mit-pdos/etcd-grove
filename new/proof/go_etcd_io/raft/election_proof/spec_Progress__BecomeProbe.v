Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [pr.BecomeProbe()] moves a [Progress] back to probing
    ([Progress__BecomeProbeⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:249;
    progress.go:130):

        if pr.State == StateSnapshot {
          pendingSnapshot := pr.PendingSnapshot
          pr.ResetState(StateProbe)
          pr.Next = max(pr.Match+1, pendingSnapshot+1)
        } else {
          pr.ResetState(StateProbe)
          pr.Next = pr.Match + 1
        }
        pr.sentCommit = min(pr.sentCommit, pr.Next-1)

    One exit, no panic of its own; the one call is [ResetState]
    ([spec_Progress__ResetState.v], exact), which empties the [Inflights]
    and clears [MsgAppFlowPaused] and [PendingSnapshot].  [Match] is
    untouched.  The [+1]/[-1] are [uint64] arithmetic and wrap silently in
    Go (and as [word.add]/[word.sub] in Goose), so they are stated that way
    rather than excluded by a premise: [own_progress] bounds neither
    [Match] nor [PendingSnapshot].  [min]/[max] are [w64_min]/[w64_max]
    ([inv_tracker.v]), Goose's builtins verbatim.

    The new state is [StateProbe = W64 0], which keeps [progress_state_ok]. *)
Definition progress_become_probe_next (pv : tracker.Progress.t) : w64 :=
  if decide (pv.(tracker.Progress.State') = W64 2) then
    w64_max (word.add pv.(tracker.Progress.Match') (W64 1))
            (word.add pv.(tracker.Progress.PendingSnapshot') (W64 1))
  else word.add pv.(tracker.Progress.Match') (W64 1).

Definition progress_become_probe (pv : tracker.Progress.t) : tracker.Progress.t :=
  pv <| tracker.Progress.MsgAppFlowPaused' := false |>
     <| tracker.Progress.PendingSnapshot' := W64 0 |>
     <| tracker.Progress.State' := W64 0 |>
     <| tracker.Progress.Next' := progress_become_probe_next pv |>
     <| tracker.Progress.sentCommit' :=
          w64_min pv.(tracker.Progress.sentCommit')
                  (word.sub (progress_become_probe_next pv) (W64 1)) |>.

Definition wp_Progress__BecomeProbe_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (pv : tracker.Progress.t) (iv : tracker.Inflights.t),
  {{{ is_pkg_init tracker ∗ "Hpr" ∷ own_progress pr pv iv }}}
    pr @! (go.PointerType tracker.Progress) @! "BecomeProbe" #()
  {{{ RET #();
      own_progress pr (progress_become_probe pv)
        (iv <| tracker.Inflights.start' := W64 0 |>
            <| tracker.Inflights.count' := W64 0 |>
            <| tracker.Inflights.bytes' := W64 0 |>) }}}.

Module Type PROGRESS__BECOMEPROBE.
  Parameter wp_Progress__BecomeProbe : wp_Progress__BecomeProbe_body.
  Arguments wp_Progress__BecomeProbe {_ _ _ _ _ _ _ _}.
End PROGRESS__BECOMEPROBE.
