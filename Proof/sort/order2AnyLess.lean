/-
The proof of `sort.order2` for any `Less` (`Spec/sort/order2AnyLess.lean`), as Perennial's (`Perennial/Proof/sort/order2.lean`).
-/
module

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

theorem sort.order2.wp_proofAnyLess :
    EtcdGrove.sort.order2.anyLessSpec (GF := GF) (hG := hG) := fun E x R l a b swaps_l swaps => by
  wp_start as ⟨#Hs, Hl, Hswaps, %Hab⟩
  wp_auto
  list_elem l (sint.nat a) as xa
  list_elem l (sint.nat b) as xb
  wp_apply wp_any_Less x R l b a xb xa (by word) (by word) Hxb_lookup Hxa_lookup $$ [$Hs $Hl]
    as %r Hl
  cases r
  · (try bool_if)
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    left; exact ⟨rfl, rfl⟩
  · (try bool_if)
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    right; exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
