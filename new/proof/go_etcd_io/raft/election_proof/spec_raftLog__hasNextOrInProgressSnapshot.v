Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** Added back 2026-09-16: deleted earlier that day as "reachable from no
    proof", which was only true because [promotable] was an [Axiom].
    [promotable]'s body calls this, and its postcondition
    [b = bool_decide (id ∈ cfg)] is only derivable if this returns [false]. *)
Definition wp_raftLog__hasNextOrInProgressSnapshot_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc),
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "hasNextOrInProgressSnapshot" #()
  {{{ (b : bool), RET #b; own_raftLog l ∗ ⌜ b = false ⌝ }}}.

Module Type RAFTLOG__HASNEXTORINPROGRESSSNAPSHOT.
  Parameter wp_raftLog__hasNextOrInProgressSnapshot : wp_raftLog__hasNextOrInProgressSnapshot_body.
  Arguments wp_raftLog__hasNextOrInProgressSnapshot {_ _ _ _ _ _ _ _}.
End RAFTLOG__HASNEXTORINPROGRESSSNAPSHOT.
