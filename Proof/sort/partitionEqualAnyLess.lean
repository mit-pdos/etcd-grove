/-
The proof of `sort.partitionEqual` for any `Less` (`Spec/sort/partitionEqualAnyLess.lean`): the loop of Perennial's proof (`Perennial/Proof/sort/partitionEqual.lean`), without the order (`anyPartInv`, as `partition`'s).
-/
module

public import Spec.sort.partitionEqualAnyLess
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

theorem sort.partitionEqual.wp_proofAnyLess :
    EtcdGrove.sort.partitionEqual.anyLessSpec (GF := GF) (hG := hG) := fun E x R l a b pivot => by
  wp_start as ⟨#Hs, Hl0, %Hab_bound⟩
  wp_auto
  list_elem l (sint.nat pivot) as xp
  list_elem l (sint.nat a) as xa0
  wp_apply wp_any_Swap x R l a pivot xa0 xp (by omega) (by omega)
    Hxa0_lookup Hxp_lookup $$ [$Hs $Hl0] as %l1 ⟨Hl, %HP0⟩
  (try wp_auto)
  ipersist a
  ipersist data
  ihave HI : anyPartInv R l a b i_ptr j_ptr $$ [Hl i j]
  · unfold anyPartInv
    iexists l1, _, _
    iframe
    ipureintro
    exact ⟨by word, HP0⟩
  wp_for
  any_part_loop i_val
  any_part_loop j_val
  unfold anyPartInv
  iNamed HI
  have Hlen2 := HPerm1.length_eq
  (try wp_auto)
  wp_if_destruct
  · wp_for_post
    iapply HΦ
    iframe Hl
    ipureintro
    exact ⟨HPerm1, by word, by word⟩
  · any_part_swap
    wp_for_post
    unfold anyPartInv
    iframe

end proof

end EtcdGrove
end Perennial
