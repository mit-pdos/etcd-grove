(** * [slices.Sort], which Goose has not translated *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.defs.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** [campaign] calls [slices.Sort] to put the voter ids in a deterministic
    order.  That function is **not translated**: [new/code/slices.v] declares
    the name but there is no [slices.Sortⁱᵐᵖˡ] and no [FuncUnfold] for it in
    [slices.Assumptions] -- only [SortFunc] is translated, and
    [New.proof.slices_proof.sort] proves [wp_SortFunc] against that.  So the
    call cannot be stepped, and this axiom is what stands in for it.

    The postcondition is **only** that the slice is permuted.  Sortedness is
    never used: [step_campaign] accepts any permutation of
    [elements (cfg ∖ {[id]})], because the order in which a candidate sends
    its vote requests is not observable in the model.  That makes this a
    weak axiom -- it would follow from [wp_SortFunc]'s [Hperm] conjunct
    alone.

    To discharge it rather than assume it: add [slices.Sort] to the
    translated set in [new/etc/update-goose-new.py], regenerate, and derive
    it from [wp_SortFunc]. *)
Axiom wp_slices_Sort : ∀ (data : slice.t) (xs : list w64),
  {{{ is_pkg_init slices ∗ data ↦* xs }}}
    #(functions slices.Sort [go.SliceType go.uint64; go.uint64]) #data
  {{{ (xs' : list w64), RET #();
      data ↦* xs' ∗ ⌜ xs ≡ₚ xs' ⌝ }}}.

End proof.
