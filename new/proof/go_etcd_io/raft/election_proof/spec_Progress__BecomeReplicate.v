Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [pr.BecomeReplicate()] moves a [Progress] into the replicating state
    ([Progress__BecomeReplicateⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v;
    progress.go):

      pr.ResetState(StateReplicate)
      pr.Next = pr.Match + 1

    It says nothing about votes, terms or roles, so the model does not see
    it.  The new record is [progress_become_replicate p] ([defs.v]); it
    leaves [matched] alone (Match discipline,
    notes/raft-replication-model.md).  [pr.Match + 1] is [uint64]
    arithmetic and wraps, so it is [word.add]. *)
Definition wp_Progress__BecomeReplicate_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (p : progress.t),
  {{{ is_pkg_init tracker ∗ own_Progress pr p }}}
    pr @! (go.PointerType tracker.Progress) @! "BecomeReplicate" #()
  {{{ RET #(); own_Progress pr (progress_become_replicate p) }}}.

Module Type PROGRESS__BECOMEREPLICATE.
  Parameter wp_Progress__BecomeReplicate : wp_Progress__BecomeReplicate_body.
  Arguments wp_Progress__BecomeReplicate {_ _ _ _ _ _ _ _}.
End PROGRESS__BECOMEREPLICATE.
