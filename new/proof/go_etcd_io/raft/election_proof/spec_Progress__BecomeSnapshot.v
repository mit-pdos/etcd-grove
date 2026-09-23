Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [pr.BecomeSnapshot(snapshoti)] moves a [Progress] into [StateSnapshot]
    and records the pending snapshot index
    ([Progress__BecomeSnapshotⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:290):

      pr.ResetState(StateSnapshot)
      pr.PendingSnapshot = snapshoti
      pr.Next = snapshoti + 1
      pr.sentCommit = snapshoti

    Like [BecomeReplicate], it says nothing about votes, terms or roles, so
    the model does not see it; the content of the triple is that
    [own_progress]'s invariants survive -- in particular
    [progress_state_ok], since [StateSnapshot] is one of the three legal
    states ([inv_tracker.v]). *)
Definition wp_Progress__BecomeSnapshot_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (pv : tracker.Progress.t) (iv : tracker.Inflights.t)
    (snapshoti : w64),
  {{{ is_pkg_init tracker ∗ own_progress pr pv iv }}}
    pr @! (go.PointerType tracker.Progress) @! "BecomeSnapshot" #snapshoti
  {{{ RET #(); ∃ pv' iv', own_progress pr pv' iv' }}}.

Module Type PROGRESS__BECOMESNAPSHOT.
  Parameter wp_Progress__BecomeSnapshot : wp_Progress__BecomeSnapshot_body.
  Arguments wp_Progress__BecomeSnapshot {_ _ _ _ _ _ _ _}.
End PROGRESS__BECOMESNAPSHOT.
