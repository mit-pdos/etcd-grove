/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/slices/SortFuncOn/medianCmpFunc.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Perennial's `slices.medianCmpFunc` spec and proof (Perennial/Spec/slices/medianCmpFunc.lean,
Perennial/Proof/slices/medianCmpFunc.lean) with the comparator needed only on `φ`, which every element
of the slice satisfies (Proof/slices/SortFuncOn/Basics.lean).
-/
module

public import Perennial.Proof.slices.PartitionBasics
public import Perennial.Spec.slices.medianCmpFunc
public import Perennial.Spec.slices.order2CmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.Basics
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.order2CmpFuncDefs
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

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.medianCmpFunc.wp_proofOn
    (wp_order2CmpFunc : slices.order2CmpFunc.specOn (GF := GF) (hG := hG)) :
    slices.medianCmpFunc.specOn (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R _ φ data a b c swaps_l cmp_code dq xs swaps Hφ
  wp_start as H
  iNamed H
  wp_auto
  list_elem xs (sint.nat a) as xa
  list_elem xs (sint.nat b) as xb
  list_elem xs (sint.nat c) as xc
  wp_apply wp_order2CmpFunc R φ data a b swaps_l cmp_code dq xs swaps xa xb (by omega) (by omega) Hφ
    $$ [Hxs Hswaps] with %a1 %b1 %sw1 ⟨Hxs, %Hab, Hswaps⟩
  · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxb_lookup⟩
  rcases Hab with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a1 b1
  · wp_apply wp_order2CmpFunc R φ data b c swaps_l cmp_code dq xs sw1 xb xc (by omega) (by omega) Hφ
      $$ [Hxs Hswaps] with %b2 %c2 %sw2 ⟨Hxs, %Hbc, Hswaps⟩
    · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxc_lookup⟩
    rcases Hbc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst b2 c2
    · wp_apply wp_order2CmpFunc R φ data a b swaps_l cmp_code dq xs sw2 xa xb (by omega) (by omega) Hφ
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxb_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
    · wp_apply wp_order2CmpFunc R φ data a c swaps_l cmp_code dq xs sw2 xa xc (by omega) (by omega) Hφ
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxc_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
  · wp_apply wp_order2CmpFunc R φ data a c swaps_l cmp_code dq xs sw1 xa xc (by omega) (by omega) Hφ
      $$ [Hxs Hswaps] with %b2 %c2 %sw2 ⟨Hxs, %Hbc, Hswaps⟩
    · iframe; iframe #; ipureintro; exact ⟨Hxa_lookup, Hxc_lookup⟩
    rcases Hbc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst b2 c2
    · wp_apply wp_order2CmpFunc R φ data b a swaps_l cmp_code dq xs sw2 xb xa (by omega) (by omega) Hφ
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxa_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp
    · wp_apply wp_order2CmpFunc R φ data b c swaps_l cmp_code dq xs sw2 xb xc (by omega) (by omega) Hφ
        $$ [Hxs Hswaps] with %a3 %b3 %sw3 ⟨Hxs, %Hab3, Hswaps⟩
      · iframe; iframe #; ipureintro; exact ⟨Hxb_lookup, Hxc_lookup⟩
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> subst a3 b3 <;> simp

end proof

end Perennial
