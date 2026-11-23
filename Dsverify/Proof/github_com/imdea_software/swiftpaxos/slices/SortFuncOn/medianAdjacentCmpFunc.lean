/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/slices/SortFuncOn/medianAdjacentCmpFunc.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Perennial's `slices.medianAdjacentCmpFunc` spec and proof (Perennial/Spec/slices/medianAdjacentCmpFunc.lean,
Perennial/Proof/slices/medianAdjacentCmpFunc.lean) with the comparator needed only on `φ`, which every element
of the slice satisfies (Proof/slices/SortFuncOn/Basics.lean).
-/
module

public import Perennial.Proof.slices.PartitionBasics
public import Perennial.Spec.slices.medianAdjacentCmpFunc
public import Perennial.Spec.slices.medianCmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.Basics
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.medianCmpFunc

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec

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

variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.medianAdjacentCmpFunc.wp_proofOn
    (wp_medianCmpFunc : slices.medianCmpFunc.specOn (GF := GF) (hG := hG)) :
    slices.medianAdjacentCmpFunc.specOn (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R _ φ data a swaps_l cmp_code dq xs swaps Hφ
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_medianCmpFunc R φ data (a - W64 1) a (a + W64 1) swaps_l cmp_code dq xs swaps Hφ
    $$ [Hxs Hswaps] with %r %sw ⟨Hxs, %Hr, Hswaps⟩
  · iframe; iframe #; ipureintro; word
  iapply HΦ; iframe; ipureintro
  rcases Hr with rfl | rfl | rfl <;> word

end proof

end Perennial
