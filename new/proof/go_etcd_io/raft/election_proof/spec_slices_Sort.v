Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [campaign] calls [slices.Sort] to put the voter ids in a deterministic
    order.  That function is **not translated**: [new/code/slices.v] declares
    the name but there is no [slices.Sortⁱᵐᵖˡ] and no [FuncUnfold] for it in
    [slices.Assumptions] -- only [SortFunc] is translated, and
    [New.proof.slices_proof.sort] proves [wp_SortFunc] against that.  So the
    call cannot be stepped, and this axiom is what stands in for it.

    The postcondition is that the slice is permuted **and sorted
    ascending** -- [wp_SortFunc]'s [Hperm] and [Hsorted] conjuncts at the
    order [<] on [uint.Z], which is what Go's [slices.Sort] does on
    [uint64] ([cmp.Less]).  Sortedness was not stated until 2026-10-01:
    [campaign], [Visit], [VoterNodes] and [MajorityConfig.Slice] need only
    the permutation ([step_campaign] accepts any order of vote requests).
    [MajorityConfig.CommittedIndex] needs the order -- it reads the quorum
    index off the sorted acknowledgements at a fixed position -- so the
    axiom was strengthened then, and only by that conjunct.

    To discharge it rather than assume it: add [slices.Sort] to the
    translated set in [new/etc/update-goose-new.py], regenerate, and derive
    it from [wp_SortFunc]. *)
Definition wp_slices_Sort_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions),
  ∀ (data : slice.t) (xs : list w64),
  {{{ is_pkg_init slices ∗ data ↦* xs }}}
    #(functions slices.Sort [go.SliceType go.uint64; go.uint64]) #data
  {{{ (xs' : list w64), RET #();
      data ↦* xs' ∗ ⌜ xs ≡ₚ xs' ⌝ ∗
      ⌜ ∀ (i j : nat) (xi xj : w64), xs' !! i = Some xi → xs' !! j = Some xj →
          (i < j)%nat → uint.Z xi ≤ uint.Z xj ⌝ }}}.

Module Type SLICES_SORT.
  Parameter wp_slices_Sort : wp_slices_Sort_body.
  Arguments wp_slices_Sort {_ _ _ _ _ _ _ _}.
End SLICES_SORT.
