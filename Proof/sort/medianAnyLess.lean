/-
The proof of `sort.median` for any `Less` (`Spec/sort/medianAnyLess.lean`), as Perennial's (`Perennial/Proof/sort/median.lean`).
-/
module

public import Spec.sort.medianAnyLess
public import Spec.sort.order2AnyLess
public import Proof.sort.AnyLessBasics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open sortAny

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

theorem sort.median.wp_proofAnyLess
    (wp_order2 : EtcdGrove.sort.order2.anyLessSpec (GF := GF) (hG := hG)) :
    EtcdGrove.sort.median.anyLessSpec (GF := GF) (hG := hG) := fun E x R l a b c swaps_l swaps => by
  wp_start as ⟨#Hs, Hl, Hswaps, %Hb⟩
  wp_auto
  wp_apply wp_order2 E x R l a b swaps_l swaps $$ [Hl Hswaps] with %a1 %b1 %sw1 ⟨Hl, Hswaps, %Hab⟩
  · iframe; iframe #; ipureintro; omega
  rcases Hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst a1 b1
  · wp_apply wp_order2 E x R l b c swaps_l sw1 $$ [Hl Hswaps]
      with %b2 %c2 %sw2 ⟨Hl, Hswaps, %Hbc⟩
    · iframe; iframe #; ipureintro; omega
    rcases Hbc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst b2 c2
    · wp_apply wp_order2 E x R l a b swaps_l sw2 $$ [Hl Hswaps]
        with %a3 %b3 %sw3 ⟨Hl, Hswaps, %Hab3⟩
      · iframe; iframe #; ipureintro; omega
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst a3 b3 <;> simp
    · wp_apply wp_order2 E x R l a c swaps_l sw2 $$ [Hl Hswaps]
        with %a3 %b3 %sw3 ⟨Hl, Hswaps, %Hab3⟩
      · iframe; iframe #; ipureintro; omega
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst a3 b3 <;> simp
  · wp_apply wp_order2 E x R l a c swaps_l sw1 $$ [Hl Hswaps]
      with %b2 %c2 %sw2 ⟨Hl, Hswaps, %Hbc⟩
    · iframe; iframe #; ipureintro; omega
    rcases Hbc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst b2 c2
    · wp_apply wp_order2 E x R l b a swaps_l sw2 $$ [Hl Hswaps]
        with %a3 %b3 %sw3 ⟨Hl, Hswaps, %Hab3⟩
      · iframe; iframe #; ipureintro; omega
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst a3 b3 <;> simp
    · wp_apply wp_order2 E x R l b c swaps_l sw2 $$ [Hl Hswaps]
        with %a3 %b3 %sw3 ⟨Hl, Hswaps, %Hab3⟩
      · iframe; iframe #; ipureintro; omega
      iapply HΦ; iframe; ipureintro
      rcases Hab3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst a3 b3 <;> simp

end proof

end EtcdGrove
end Perennial
