Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [pr.MaybeDecrTo(rejected, matchHint)] reacts to a rejected [MsgApp]
    ([Progress__MaybeDecrToⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:400;
    progress.go:226):

        if pr.State == StateReplicate {
          if rejected <= pr.Match { return false }            // exit 1: stale
          pr.Next = pr.Match + 1
          pr.sentCommit = min(pr.sentCommit, pr.Next-1)
          return true                                          // exit 2
        }
        if pr.Next-1 != rejected { return false }              // exit 3: stale
        pr.Next = max(min(rejected, matchHint+1), pr.Match+1)
        pr.sentCommit = min(pr.sentCommit, pr.Next-1)
        pr.MsgAppFlowPaused = false
        return true                                            // exit 4

    Four exits, no panic, no call ([min]/[max] are builtins).  [Match],
    [State] and the [Inflights] are never written.  Every [+1]/[-1] is
    [uint64] arithmetic, which Go wraps silently and Goose renders as
    [word.add]/[word.sub] -- [own_Progress] bounds neither [Next] nor
    [Match], so [pr.Next-1] at [Next = 0] and [pr.Match+1] at
    [Match = 2^64-1] really do wrap.  The postcondition therefore states the
    body's arithmetic verbatim rather than excluding the wrap by a premise;
    [w64_min]/[w64_max] ([defs.v]) are Goose's [min]/[max].
    [progress_maybe_decr_to p rejected matchHint] ([defs.v]) is the pair
    (result, new record), the four exits in order. *)
Definition wp_Progress__MaybeDecrTo_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (p : progress.t) (rejected matchHint : w64),
  {{{ is_pkg_init tracker ∗ "Hpr" ∷ own_Progress pr p }}}
    pr @! (go.PointerType tracker.Progress) @! "MaybeDecrTo" #rejected #matchHint
  {{{ RET #((progress_maybe_decr_to p rejected matchHint).1);
      own_Progress pr (progress_maybe_decr_to p rejected matchHint).2 }}}.

Module Type PROGRESS__MAYBEDECRTO.
  Parameter wp_Progress__MaybeDecrTo : wp_Progress__MaybeDecrTo_body.
  Arguments wp_Progress__MaybeDecrTo {_ _ _ _ _ _ _ _}.
End PROGRESS__MAYBEDECRTO.
