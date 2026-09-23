Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** ** The [unstable] suffix

    Three [maybe*] methods, all on a bare [*unstable] so they can be reused
    wherever the field is split out.  Each takes [snapshot = nil] as a
    premise -- with a snapshot present all three have an extra branch, and
    none of them is reachable under our scope. *)
Definition wp_unstable__maybeFirstIndex_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (u : loc) (uv : raft.unstable.t),
  uv.(raft.unstable.snapshot') = null →
  {{{ is_pkg_init raft ∗ u ↦ uv }}}
    u @! (go.PointerType raft.unstable) @! "maybeFirstIndex" #()
  {{{ (i : w64), RET (#i, #false); u ↦ uv }}}.

Module Type UNSTABLE__MAYBEFIRSTINDEX.
  Parameter wp_unstable__maybeFirstIndex : wp_unstable__maybeFirstIndex_body.
  Arguments wp_unstable__maybeFirstIndex {_ _ _ _ _ _ _ _}.
End UNSTABLE__MAYBEFIRSTINDEX.
