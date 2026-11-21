/-
The proof of `sort.reverseRange` for any `Less` (`Spec/sort/reverseRangeAnyLess.lean`): the loop of Perennial's proof (`Perennial/Proof/sort/reverseRange.lean`), without the order.
-/
module

public import Spec.sort.reverseRangeAnyLess
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

theorem sort.reverseRange.wp_proofAnyLess :
    EtcdGrove.sort.reverseRange.anyLessSpec (GF := GF) (hG := hG) := fun E x R l a b => by
  wp_start as ⟨#Hs, Hl, %Hab⟩
  wp_auto
  ihave HI : (∃ (l1 : List E) (i_val j_val : w64),
      "Hl" ∷ R l1 ∗
      "i" ∷ i_ptr ↦ i_val ∗
      "j" ∷ j_ptr ↦ j_val ∗
      "%ij_bound" ∷ ⌜sint.Z a ≤ sint.Z i_val ∧ sint.Z j_val < sint.Z b⌝ ∗
      "%HPerm1" ∷ ⌜l.Perm l1⌝ : IProp GF) $$ [Hl i j]
  · iexists l, _, _
    iframe
    ipureintro
    exact ⟨by word, List.Perm.refl _⟩
  wp_for HI
  wp_if_destruct
  · have Hlen := HPerm1.length_eq
    list_elem l1 (sint.nat j_val) as xj
    list_elem l1 (sint.nat i_val) as xi
    wp_apply wp_any_Swap x R l1 i_val j_val xi xj (by word) (by word)
      Hxi_lookup Hxj_lookup $$ [$Hs $Hl] as %l2 ⟨Hl, %Hp⟩
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    exact ⟨by word, HPerm1.trans Hp⟩
  · iapply HΦ
    iframe
    ipureintro
    exact HPerm1

end proof

end EtcdGrove
end Perennial
