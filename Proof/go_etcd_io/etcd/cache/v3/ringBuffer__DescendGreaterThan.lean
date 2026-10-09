/-
Proof of `Spec/ringBuffer__DescendGreaterThan.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__DescendGreaterThan
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__findLastIndexLessOrEqual
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

theorem ringBuffer.DescendGreaterThan.wp_proof
    (wp_findLastIndexLessOrEqual :
      ringBuffer.findLastIndexLessOrEqual.spec (GF := GF) (hG := hG))
    (wp_at : ringBuffer.«at».spec (GF := GF) (hG := hG)) :
    ringBuffer.DescendGreaterThan.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V r cap isItem revOf items pivot iter P Q
  wp_start as ⟨H, HP, #Hiter⟩
  iunfold iterSpec at Hiter
  ihave %Hn := ownRingBuffer_length r cap isItem revOf items $$ H
  have Hk := leCount_le revOf pivot items
  have Hkw : sint.Z (W64 ((leCount revOf pivot items : Int) - 1)) =
      (leCount revOf pivot items : Int) - 1 := by
    have := Hn.2; word
  icases ownRingBuffer_struct_acc r cap isItem revOf items $$ H with ⟨%rb, Hr, %Hsz, Hclose⟩
  wp_auto
  ihave H := Hclose $$ Hr
  -- `m` items visited, `i = n - 1 - m`; the bound `k - 1` is recomputed by every test
  ihave HI : iprop(∃ (j : w64) (m : Nat),
      "i" ∷ i_ptr ↦ j ∗
      "H" ∷ ownRingBuffer r cap isItem revOf items ∗
      "HP" ∷ P m ∗
      "%Hm" ∷ ⌜sint.Z j = (items.length : Int) - 1 - m ∧
        m ≤ items.length - leCount revOf pivot items⌝) $$ [i H HP]
  · iexists _, 0
    simp only [named]
    iframe
    ipureintro
    constructor
    · have := Hn.2; word
    · omega
  wp_for HI
  wp_apply wp_findLastIndexLessOrEqual $$ [$H] as H
  cleanup_bool_decide
  wp_if_destruct
  · -- visit item `n - 1 - m`
    have Hlt : m < items.length - leCount revOf pivot items := by omega
    wp_apply wp_at $$ [$H] as %e %v ⟨H, % ⟨Hv, Herev⟩, Hit⟩
    · ipureintro; omega
    rw [show sint.nat j = items.length - 1 - m by
      simp only [sint.nat, Hm.1]; omega] at Hv
    have Hvis : (descendGtVisited revOf pivot items)[m]? = some v := by
      simp only [descendGtVisited]
      rw [List.getElem?_reverse' (j := items.length - leCount revOf pivot items - 1 - m)
        (by simp only [List.length_drop]; omega), List.getElem?_drop]
      rw [show leCount revOf pivot items + (items.length - leCount revOf pivot items - 1 - m) =
        items.length - 1 - m by omega]
      exact Hv
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
      iexists j - W64 1, m + 1
      simp only [named]
      iframe
      ipureintro
      constructor
      · have := Hn.2; push_cast; word
      · omega
  · -- every item above `pivot` visited
    have Hlen : (descendGtVisited revOf pivot items).length = m := by
      simp only [descendGtVisited, List.length_reverse, List.length_drop]; omega
    iapply HΦ
    iframe H
    iright
    rw [Hlen]
    iexact HP

end proof

end EtcdGrove
end Perennial
