/-
Port of election_proof/spec_slices_Sort.v (feb5c73d4).

Lean notes:
* Go's `slices.Sort` is `Perennial.slices.«Sort»` in the generated code (`Sort` is a
  Lean keyword); the type arguments `[go.SliceType go.uint64; go.uint64]` are
  `[go.GoType.SliceType go.uint64, go.uint64]`.
* Rocq's `xs' !! i` (`i : nat`) is `xs'[i]?`.
-/
import EtcdGrove.Raft.InvRaftPhys

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

The postcondition is that the slice is permuted **and sorted ascending** --
`wp_SortFunc`'s `Hperm` and `Hsorted` conjuncts at the order `<` on `uint.Z`, which is
what Go's `slices.Sort` does on `uint64` (`cmp.Less`). Sortedness was not stated until
2026-10-01: `campaign`, `Visit`, `VoterNodes` and `MajorityConfig.Slice` need only the
permutation (`Step.campaign` accepts any order of vote requests).
`MajorityConfig.CommittedIndex` needs the order -- it reads the quorum index off the
sorted acknowledgements at a fixed position -- so the axiom was strengthened then, and
only by that conjunct.

To discharge it rather than assume it: add `slices.Sort` to the translated set in
`new/etc/update-goose-new.py`, regenerate, and derive it from `wp_SortFunc`. -/
abbrev slices.«Sort».spec : Prop :=
  ∀ (data : GoSlice) (xs : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗ data ↦* xs }}
    (App (Val #(functions _root_.Perennial.slices.«Sort»
        [go.GoType.SliceType go.uint64, go.uint64])) (Val #data))
  {{ (xs' : List w64), RET #();
      data ↦* xs' ∗ ⌜xs ≡ₚ xs'⌝ ∗
      ⌜∀ (i j : Nat) (xi xj : w64), xs'[i]? = some xi → xs'[j]? = some xj →
          i < j → uint.Z xi ≤ uint.Z xj⌝ }}

end spec

end EtcdGrove
end Perennial
