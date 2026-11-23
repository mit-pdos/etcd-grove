/-
The definitions, specs and lemmas of `pdqsortCmpFunc.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Perennial.Proof.slices.PdqSortBasics
public import Perennial.Spec.slices.breakPatternsCmpFunc
public import Perennial.Spec.slices.choosePivotCmpFunc
public import Perennial.Spec.slices.heapSortCmpFunc
public import Perennial.Spec.slices.insertionSortCmpFunc
public import Perennial.Spec.slices.partialInsertionSortCmpFunc
public import Perennial.Spec.slices.partitionCmpFunc
public import Perennial.Spec.slices.partitionEqualCmpFunc
public import Perennial.Spec.slices.pdqsortCmpFunc
public import Perennial.Spec.slices.reverseRangeCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.Basics
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.breakPatternsCmpFuncDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.choosePivotCmpFuncDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.heapSortCmpFuncDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.insertionSortCmpFuncDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.partialInsertionSortCmpFuncDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.partitionCmpFuncDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.partitionEqualCmpFuncDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.reverseRangeCmpFuncDefs
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

abbrev slices.pdqsortCmpFunc.specOn : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] (R : E → E → Prop) [StrictWeakOrder R] (φ : E → Prop) (data : GoSlice)
    (a b limit : w64) (cmp_code : GoFunc) (xs : List E) (Hφ : AllOn φ xs),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a ≤ sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "%Header" ∷ ⌜header R xs (sint.nat a) (sint.nat b)⌝ ∗
        "#Hcmp" ∷ cmpOn R φ cmp_code }}
      (App (App (App (App (App (Val #(functions pdqsortCmpFunc [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #limit)) (Val #cmp_code))
    {{ (xs' : List E), RET #();
        "Hxs" ∷ data ↦* xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜IsSortedSeg R xs' (sint.nat a) (sint.nat b)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

end proof

end Perennial
