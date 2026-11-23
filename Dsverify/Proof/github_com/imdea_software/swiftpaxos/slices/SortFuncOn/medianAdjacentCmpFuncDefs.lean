/-
The definitions, specs and lemmas of `medianAdjacentCmpFunc.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Perennial.Proof.slices.PartitionBasics
public import Perennial.Spec.slices.medianAdjacentCmpFunc
public import Perennial.Spec.slices.medianCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.Basics
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.medianCmpFuncDefs
@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

abbrev slices.medianAdjacentCmpFunc.specOn : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] (R : E → E → Prop) [StrictWeakOrder R] (φ : E → Prop) (data : GoSlice)
    (a : w64) (swaps_l : Loc) (cmp_code : GoFunc) (dq : DFrac) (xs : List E) (swaps : w64) (Hφ : AllOn φ xs),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦*{dq} xs ∗
        "%Hbounds" ∷ ⌜(1 ≤ sint.Z a ∧ sint.Z a < (xs.length : Int) - 1) ∧ xs.length ≤ 2 ^ 62⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hcmp" ∷ cmpOn R φ cmp_code }}
      (App (App (App (App (Val #(functions medianAdjacentCmpFunc [Et])) (Val #data)) (Val #a))
        (Val #swaps_l)) (Val #cmp_code))
    {{ (r : w64) (swaps' : w64), RET #r;
        data ↦*{dq} xs ∗
        ⌜sint.Z a - 1 ≤ sint.Z r ∧ sint.Z r ≤ sint.Z a + 1⌝ ∗
        swaps_l ↦ swaps' }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

end proof

end Perennial
