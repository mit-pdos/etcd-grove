/-
Proof of `Spec/ringBuffer__DescendLessOrEqual.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.ringBuffer__DescendLessOrEqual
import EtcdGrove.Cache.Spec.ringBuffer__findLastIndexLessOrEqual
import EtcdGrove.Cache.Spec.ringBuffer__at

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

theorem ringBuffer.DescendLessOrEqual.wp_proof
    (wp_findLastIndexLessOrEqual :
      ringBuffer.findLastIndexLessOrEqual.spec (GF := GF) (hG := hG))
    (wp_at : ringBuffer.«at».spec (GF := GF) (hG := hG)) :
    ringBuffer.DescendLessOrEqual.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V r cap isItem revOf items pivot iter P Q
  wp_start as ⟨H, HP, #Hiter⟩
  wp_auto
  wp_apply wp_findLastIndexLessOrEqual $$ [$H] as H
  iunfold iterSpec at Hiter
  ihave %Hn := ownRingBuffer_length r cap isItem revOf items $$ H
  have Hk := leCount_le revOf pivot items
  -- `m` items visited, `i = k - 1 - m`
  ihave HI : iprop(∃ (j : w64) (m : Nat),
      "i" ∷ i_ptr ↦ j ∗
      "H" ∷ ownRingBuffer r cap isItem revOf items ∗
      "HP" ∷ P m ∗
      "%Hm" ∷ ⌜sint.Z j = (leCount revOf pivot items : Int) - 1 - m ∧
        m ≤ leCount revOf pivot items⌝) $$ [i H HP]
  · iexists _, 0
    simp only [named]
    iframe
    ipureintro
    constructor
    · have := Hn.2; word
    · omega
  wp_for HI
  have H0 : sint.Z (W64 0) = 0 := by word
  wp_if_destruct
  · -- visit item `k - 1 - m`
    have Hlt : m < leCount revOf pivot items := by omega
    wp_apply wp_at $$ [$H] as %e %v ⟨H, % ⟨Hv, Herev⟩, Hit⟩
    · ipureintro; omega
    rw [show sint.nat j = leCount revOf pivot items - 1 - m by
      simp only [sint.nat, Hm.1]; omega] at Hv
    have Hvis : (descendLeVisited revOf pivot items)[m]? = some v := by
      simp only [descendLeVisited]
      rw [List.getElem?_reverse' (j := leCount revOf pivot items - 1 - m)
        (by simp only [List.length_take]; omega), List.getElem?_take,
        ite_eq_left (by omega)]
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
  · -- every item at or below `pivot` visited
    have Hlen : (descendLeVisited revOf pivot items).length = m := by
      simp only [descendLeVisited, List.length_reverse, List.length_take, Nat.min_eq_left Hk]
      omega
    iapply HΦ
    iframe H
    iright
    rw [Hlen]
    iexact HP

end proof

end EtcdGrove
end Perennial
