Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [l.hasNextOrInProgressSnapshot()] is [l.unstable.snapshot != nil]:
    whether a snapshot is pending ([logstate.snap]).  [promotable] calls it
    -- a node with a pending snapshot does not campaign.  (Added back
    2026-09-16, when [promotable] stopped being an [Axiom]; until
    2026-10-02 it returned [false] outright, no snapshot being in scope.) *)
Definition wp_raftLog__hasNextOrInProgressSnapshot_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t),
  {{{ is_pkg_init raft ∗ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "hasNextOrInProgressSnapshot" #()
  {{{ (b : bool), RET #b; own_raftLog l ls ∗ ⌜ b = bool_decide (ls.(logstate.snap) ≠ None) ⌝ }}}.

Module Type RAFTLOG__HASNEXTORINPROGRESSSNAPSHOT.
  Parameter wp_raftLog__hasNextOrInProgressSnapshot : wp_raftLog__hasNextOrInProgressSnapshot_body.
  Arguments wp_raftLog__hasNextOrInProgressSnapshot {_ _ _ _ _ _ _ _}.
End RAFTLOG__HASNEXTORINPROGRESSSNAPSHOT.
