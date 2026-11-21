/-
The proof of `sort.partition` for any `Less` (`Spec/sort/partitionAnyLess.lean`): the loops of Perennial's proof (`Perennial/Proof/sort/partition.lean`, its macros in `PartitionBasics.lean`), without the order: `i` stays in `[a+1, b]` and `j` in `[a, b-1]` (`anyPartInv`), since each inner loop tests `i <= j` before `Less`.
-/
module

public import Spec.sort.partitionAnyLess
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

theorem sort.partition.wp_proofAnyLess :
    EtcdGrove.sort.partition.anyLessSpec (GF := GF) (hG := hG) := fun E x R l a b pivot => by
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
  any_part_loop i_val
  any_part_loop j_val
  unfold anyPartInv
  iNamed HI
  have Hlen2 := HPerm1.length_eq
  (try wp_auto)
  wp_if_destruct
  · list_elem L (sint.nat j_val) as xj
    list_elem L (sint.nat a) as xa
    wp_apply wp_any_Swap x R L j_val a xj xa (by word) (by word) Hxj_lookup Hxa_lookup
      $$ [$Hs $Hl] as %L3 ⟨Hl, %HP3⟩
    (try wp_auto)
    iapply HΦ
    iframe Hl
    ipureintro
    exact ⟨HPerm1.trans HP3, by word, by word⟩
  · any_part_swap
    clear HP2 L2 HPerm1 ij_bound Hlen2 Hxi_lookup Hxj_lookup Hif Hle L i_val j_val xi xj
    wp_for
    any_part_loop i_val
    any_part_loop j_val
    unfold anyPartInv
    iNamed HI
    have Hlen2 := HPerm1.length_eq
    (try wp_auto)
    wp_if_destruct
    · wp_for_post
      list_elem L (sint.nat j_val) as xj
      list_elem L (sint.nat a) as xa
      wp_apply wp_any_Swap x R L j_val a xj xa (by word) (by word) Hxj_lookup Hxa_lookup
        $$ [$Hs $Hl] as %L3 ⟨Hl, %HP3⟩
      (try wp_auto)
      iapply HΦ
      iframe Hl
      ipureintro
      exact ⟨HPerm1.trans HP3, by word, by word⟩
    · any_part_swap
      wp_for_post
      unfold anyPartInv
      iframe

end proof

end EtcdGrove
end Perennial
