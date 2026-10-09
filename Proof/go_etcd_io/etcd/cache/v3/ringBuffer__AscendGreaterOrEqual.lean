/-
Proof of `Spec/ringBuffer__AscendGreaterOrEqual.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__AscendGreaterOrEqual
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__findFirstIndexGreaterOrEqual
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__at

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem ringBuffer.AscendGreaterOrEqual.wp_proof
    (wp_findFirstIndexGreaterOrEqual :
      ringBuffer.findFirstIndexGreaterOrEqual.spec (GF := GF) (hG := hG))
    (wp_at : ringBuffer.«at».spec (GF := GF) (hG := hG)) :
    ringBuffer.AscendGreaterOrEqual.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V r cap isItem revOf items pivot iter P Q
  wp_start as ⟨H, HP, #Hiter⟩
  wp_auto
  wp_apply wp_findFirstIndexGreaterOrEqual $$ [$H] as H
  iunfold iterSpec at Hiter
  ihave %Hn := ownRingBuffer_length r cap isItem revOf items $$ H
  have Hk := ltCount_le revOf pivot items
  -- `m` items visited, `i = k + m`
  ihave HI : iprop(∃ (j : w64) (m : Nat),
      "i" ∷ i_ptr ↦ j ∗
      "H" ∷ ownRingBuffer r cap isItem revOf items ∗
      "HP" ∷ P m ∗
      "%Hm" ∷ ⌜sint.Z j = ((ltCount revOf pivot items + m : Nat) : Int) ∧
        ltCount revOf pivot items + m ≤ items.length⌝) $$ [i H HP]
  · iexists _, 0
    simp only [named]
    iframe
    ipureintro
    constructor
    · have := Hn.2; simp only [Nat.add_zero]; word
    · omega
  wp_for HI
  icases ownRingBuffer_struct_acc r cap isItem revOf items $$ H with ⟨%rb, Hr, %Hsz, Hclose⟩
  wp_auto
  ihave H := Hclose $$ Hr
  cleanup_bool_decide
  wp_if_destruct
  · -- visit item `k + m`
    have Hlt : ltCount revOf pivot items + m < items.length := by omega
    wp_apply wp_at $$ [$H] as %e %v ⟨H, % ⟨Hv, Herev⟩, Hit⟩
    · ipureintro; omega
    rw [show sint.nat j = ltCount revOf pivot items + m by
      simp only [sint.nat, Hm.1, Int.toNat_natCast]] at Hv
    have Hvis : (ascendGeVisited revOf pivot items)[m]? = some v := by
      simp only [ascendGeVisited, List.getElem?_drop]; exact Hv
    rw [Herev]
    wp_apply Hiter $$ %m %e.item' %v %Hvis [HP Hit] as %cont HP
    · iframe
    cases cont <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] <;> wp_auto
    · -- `iter` said stop
      wp_for_post
      iapply HΦ
      iframe H
      ileft
      iexact HP
    · wp_for_post
      iframe
      iexists j + W64 1, m + 1
      simp only [named]
      iframe
      ipureintro
      constructor
      · have := Hn.2; word
      · omega
  · -- every item from `k` on visited
    have Hlen : (ascendGeVisited revOf pivot items).length = m := by
      simp only [ascendGeVisited, List.length_drop]; omega
    iapply HΦ
    iframe H
    iright
    rw [Hlen]
    iexact HP

end proof

end EtcdGrove
end Perennial
