/-
The proof of `sort.medianAdjacent` for any `Less` (`Spec/sort/medianAdjacentAnyLess.lean`), as Perennial's (`Perennial/Proof/sort/medianAdjacent.lean`).
-/
module

public import Spec.sort.medianAdjacentAnyLess
public import Spec.sort.medianAnyLess
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

theorem sort.medianAdjacent.wp_proofAnyLess
    (wp_median : EtcdGrove.sort.median.anyLessSpec (GF := GF) (hG := hG)) :
    EtcdGrove.sort.medianAdjacent.anyLessSpec (GF := GF) (hG := hG) :=
    fun E x R l a swaps_l swaps => by
  wp_start as ⟨#Hs, Hl, Hswaps, %Hb⟩
  wp_auto
  wp_apply wp_median E x R l (a - W64 1) a (a + W64 1) swaps_l swaps $$ [Hl Hswaps]
    with %r %sw ⟨Hl, Hswaps, %Hr⟩
  · iframe; iframe #; ipureintro; word
  iapply HΦ; iframe; ipureintro
  rcases Hr with rfl | rfl | rfl <;> word

end proof

end EtcdGrove
end Perennial
