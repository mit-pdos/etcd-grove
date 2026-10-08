/-
Proof of `Spec/ringBuffer__AscendLessThan.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.ringBuffer__AscendLessThan
import EtcdGrove.Cache.Spec.ringBuffer__findFirstIndexGreaterOrEqual
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

theorem ringBuffer.AscendLessThan.wp_proof
    (wp_findFirstIndexGreaterOrEqual :
      ringBuffer.findFirstIndexGreaterOrEqual.spec (GF := GF) (hG := hG))
    (wp_at : ringBuffer.«at».spec (GF := GF) (hG := hG)) :
    ringBuffer.AscendLessThan.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V r cap isItem revOf items pivot iter P Q
  wp_start as ⟨H, HP, #Hiter⟩
  wp_auto
  iunfold iterSpec at Hiter
  ihave %Hn := ownRingBuffer_length r cap isItem revOf items $$ H
  have Hk := ltCount_le revOf pivot items
  have Hkw : sint.Z (W64 (ltCount revOf pivot items : Int)) = ltCount revOf pivot items := by
    have := Hn.2; word
  -- `m` items visited, `i = m`; the bound `k` is recomputed by every test
  ihave HI : iprop(∃ (j : w64) (m : Nat),
      "i" ∷ i_ptr ↦ j ∗
      "H" ∷ ownRingBuffer r cap isItem revOf items ∗
      "HP" ∷ P m ∗
      "%Hm" ∷ ⌜sint.Z j = (m : Int) ∧ m ≤ ltCount revOf pivot items⌝) $$ [i H HP]
  · iexists _, 0
    simp only [named]
    iframe
    ipureintro
    exact ⟨rfl, Nat.zero_le _⟩
  wp_for HI
  wp_apply wp_findFirstIndexGreaterOrEqual $$ [$H] as H
  cleanup_bool_decide
  wp_if_destruct
  · -- visit item `m`
    have Hlt : m < ltCount revOf pivot items := by omega
    wp_apply wp_at $$ [$H] as %e %v ⟨H, % ⟨Hv, Herev⟩, Hit⟩
    · ipureintro; omega
    rw [show sint.nat j = m by simp only [sint.nat, Hm.1, Int.toNat_natCast]] at Hv
    have Hvis : (ascendLtVisited revOf pivot items)[m]? = some v := by
      simp only [ascendLtVisited, List.getElem?_take, Hlt, ite_true]; exact Hv
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
      · have := Hn.2; push_cast; word
      · omega
  · -- every item below `pivot` visited
    have Hlen : (ascendLtVisited revOf pivot items).length = m := by
      simp only [ascendLtVisited, List.length_take]; omega
    iapply HΦ
    iframe H
    iright
    rw [Hlen]
    iexact HP

end proof

end EtcdGrove
end Perennial
