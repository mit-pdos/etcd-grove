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
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.medianCmpFuncDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.medianAdjacentCmpFuncDefs

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

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
