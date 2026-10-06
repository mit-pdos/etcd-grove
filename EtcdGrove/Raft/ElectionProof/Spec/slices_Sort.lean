/-
Port of `election_proof/spec_slices_Sort.v`.

Lean notes:
* Go's `slices.Sort` is `Perennial.slices.«Sort»` in the generated code (`Sort` is a
  Lean keyword); the type arguments `[go.SliceType go.uint64; go.uint64]` are
  `[go.GoType.SliceType go.uint64, go.uint64]`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `campaign` calls `slices.Sort` to put the voter ids in a deterministic order. That
function is **not translated**: `new/code/slices.v` (Lean: `Perennial/Code/slices.lean`)
declares the name but there is no `slices.Sort.impl` and no `FuncUnfold` for it in
`slices.Assumptions` -- only `SortFunc` is translated, and
`Perennial.Proof.slices_proof.sort` proves `slices.wp_SortFunc` against that. So the
call cannot be stepped, and this axiom is what stands in for it.

The postcondition is **only** that the slice is permuted. Sortedness is never used:
`Step.campaign` accepts any permutation of `elements (cfg \ {[id]})`, because the order
in which a candidate sends its vote requests is not observable in the model. That
makes this a weak axiom -- it would follow from `wp_SortFunc`'s `Hperm` conjunct alone.

To discharge it rather than assume it: add `slices.Sort` to the translated set in
`new/etc/update-goose-new.py`, regenerate, and derive it from `wp_SortFunc`. -/
abbrev slices.Sort.spec : Prop :=
  ∀ (data : GoSlice) (xs : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗ data ↦* xs }}
    (App (Val #(functions _root_.Perennial.slices.«Sort»
        [go.GoType.SliceType go.uint64, go.uint64])) (Val #data))
  {{ (xs' : List w64), RET #();
      data ↦* xs' ∗ ⌜xs ≡ₚ xs'⌝ }}

end spec

end EtcdGrove
end Perennial
