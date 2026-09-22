Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [u.maybeLastIndex()]: the last index of the unstable suffix, and whether
    there is one.  [ok] is [false] exactly when the suffix is empty.

    Stated on a bare [*unstable] rather than through [own_raftLog], so that
    [raftLog]'s own methods can split the field out and hand it over.
    [snapshot = nil] is a premise: with a snapshot present the function has an
    extra branch, and no snapshot is in scope (see [inv_raftlog.v]). *)
Definition wp_unstable__maybeLastIndex_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (u : loc) (uv : raft.unstable.t)
      (uents : list raftpb.Entry.t),
  uv.(raft.unstable.snapshot') = null →
  (uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents) < 2^64)%Z →
  {{{ is_pkg_init raft ∗ "Hu" ∷ u ↦ uv ∗
      "Hents" ∷ uv.(raft.unstable.entries') ↦* uents }}}
    u @! (go.PointerType raft.unstable) @! "maybeLastIndex" #()
  {{{ (i : w64) (ok : bool), RET (#i, #ok);
      u ↦ uv ∗ uv.(raft.unstable.entries') ↦* uents ∗
      ⌜ uents = [] → ok = false ⌝ ∗
      ⌜ uents ≠ [] → ok = true ∧
        (uint.Z i = uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents) - 1)%Z ⌝ }}}.

Module Type UNSTABLE__MAYBELASTINDEX.
  Parameter wp_unstable__maybeLastIndex : wp_unstable__maybeLastIndex_body.
  Arguments wp_unstable__maybeLastIndex {_ _ _ _ _ _ _ _}.
End UNSTABLE__MAYBELASTINDEX.
