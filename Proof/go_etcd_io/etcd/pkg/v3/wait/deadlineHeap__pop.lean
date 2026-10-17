/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/wait/deadlineHeap__pop.lean`. Lean-first (no Rocq
counterpart; pr-verify/etcd-22495, 2026-10-17).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.deadlineHeap__pop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3 waitHeap

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]

theorem wait.deadlineHeap.pop.wp_proof : wait.deadlineHeap.pop.spec (GF := GF) (hG := hG) := by
  intro hp s xs
  wp_start as ⟨Hh, Hs, Hcap, %Hpre⟩
  obtain ⟨Hheap, Hne, Hle⟩ := Hpre
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  have H0b : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len := by constructor <;> word
  simp only [H0b, _root_.and_self, ↓reduceIte]
  list_elem xs 0 as t
  wp_apply wp_load_slice_index s _ xs _ t H0b.1 $$ [Hs] as Hs
  · iframe; ipureintro; exact Ht_lookup
  (try wp_auto)
  have Hnb : 0 ≤ sint.Z (s.len - W64 1) ∧ sint.Z (s.len - W64 1) < sint.Z s.len := by
    constructor <;> word
  have Hnn : sint.nat (s.len - W64 1) = xs.length - 1 := by word
  simp only [Hnb, _root_.and_self, ↓reduceIte]
  list_elem xs (sint.nat (s.len - W64 1)) as z
  wp_apply wp_load_slice_index s _ xs _ z Hnb.1 $$ [Hs] as Hs
  · iframe; ipureintro; exact Hz_lookup
  (try wp_auto)
  try simp only [H0b, _root_.and_self, ↓reduceIte]
  wp_apply wp_store_slice_index s _ xs z $$ [Hs] as Hs
  · iframe; ipureintro; exact ⟨H0b.1, by word⟩
  (try wp_auto)
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  have Hsb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (s.len - W64 1) ∧
      sint.Z (s.len - W64 1) ≤ sint.Z s.cap := by refine ⟨by word, by word, by word⟩
  simp only [Hsb, _root_.and_self, ↓reduceIte]
  icases (ownSlice_split_all (s.len - W64 1) s _ _ ⟨Hnb.1, by word⟩).1 $$ Hs with ⟨Hs, Hlast⟩
  ihave Hcap := ownSlice_slice_absorb_capacity s _ (W64 0) (s.len - W64 1)
    ⟨by word, by word, by word⟩ $$ [$Hlast $Hcap]
  (try wp_auto)
  generalize hs2 : slice.slice s w64 (W64 0) (s.len - W64 1) = s2 at *
  have Hs2len : s2.len = s.len - W64 1 := by rw [← hs2]; simp only [slice.slice]; word
  have HN : xs.length = (xs.length - 1) + 1 := by omega
  have Hz' : xs[xs.length - 1]? = some z := by rw [← Hnn]; exact Hz_lookup
  ihave HI : (∃ (i : w64) (ys : List w64), "i" ∷ i_ptr ↦ i ∗ "Hs" ∷ s2 ↦* ys ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ xs.length - 1 ∧ siftDownInv ys (sint.nat i) ∧
        t :: ys ≡ₚ xs ∧ ys.length = xs.length - 1⌝ : IProp GF) $$ [i Hs]
  · iexists W64 0, _
    iframe
    ipureintro
    rw [Hnn]
    refine ⟨by word, by word, siftDown_init Hheap HN Hz', pop_perm HN Hz' Ht_lookup, ?_⟩
    simp only [List.length_take, List.length_set]; omega
  wp_for HI
  obtain ⟨Hi0, HiN, Hinv, Hperm, HyL⟩ := Hi
  have Hlz : sint.Z (W64 2 * i + W64 1) = 2 * sint.Z i + 1 := by word
  have Hlnat : sint.nat (W64 2 * i + W64 1) = 2 * sint.nat i + 1 := by word
  have Hnz : sint.Z (s.len - W64 1) = (xs.length - 1 : Nat) := by word
  have Hmin : ∀ x ∈ xs, uint.Z t ≤ uint.Z x := heapOk_min Hheap Ht_lookup
  wp_if_destruct
  · -- no children: done
    wp_for_post
    iapply HΦ
    iexists s2, ys
    iframe
    ipureintro
    exact ⟨Ht_lookup, Hmin, siftDown_done_leaf Hinv (by word), Hperm⟩
  have Hlb : 0 ≤ sint.Z (W64 2 * i + W64 1) ∧ sint.Z (W64 2 * i + W64 1) < sint.Z s2.len := by
    rw [Hs2len]; constructor <;> word
  have Hrz : sint.Z (W64 2 * i + W64 1 + W64 1) = 2 * sint.Z i + 2 := by word
  have Hrnat : sint.nat (W64 2 * i + W64 1 + W64 1) = 2 * sint.nat i + 2 := by word
  list_elem ys (2 * sint.nat i + 1) as vl
  -- `c`, the least child
  wp_join iprop(∃ (c vc : w64), "c" ∷ c_ptr ↦ c ∗ "Hs" ∷ s2 ↦* ys ∗ "s" ∷ s_ptr ↦ s2 ∗
      "l" ∷ l_ptr ↦ (W64 2 * i + W64 1) ∗ "r" ∷ r_ptr ↦ (W64 2 * i + W64 1 + W64 1) ∗
      "%Hc" ∷ ⌜minChild ys (sint.nat i) (sint.nat c) vc ∧ 0 ≤ sint.Z c⌝)
    at next with [c Hs s l r] as ⟨%c, %vc, c, Hs, s, l, r, %Hc⟩
  · wp_if_destruct
    · have Hrb : 0 ≤ sint.Z (W64 2 * i + W64 1 + W64 1) ∧
          sint.Z (W64 2 * i + W64 1 + W64 1) < sint.Z s2.len := by
        rw [Hs2len]; constructor <;> word
      (try wp_auto)
      try simp only [Hrb, _root_.and_self, ↓reduceIte]
      list_elem ys (2 * sint.nat i + 2) as vr
      wp_apply wp_load_slice_index s2 _ ys _ vr Hrb.1 $$ [Hs] as Hs
      · iframe; ipureintro
        rw [show (sint.Z (W64 2 * i + W64 1 + W64 1)).toNat = 2 * sint.nat i + 2 from Hrnat]
        exact Hvr_lookup
      try simp only [Hlb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index s2 _ ys _ vl Hlb.1 $$ [Hs] as Hs
      · iframe; ipureintro
        rw [show (sint.Z (W64 2 * i + W64 1)).toNat = 2 * sint.nat i + 1 from Hlnat]
        exact Hvl_lookup
      have Hpick := minChild_pick Hvl_lookup (some vr) Hvr_lookup
      wp_if_destruct
      · wp_join_done
        iexists _, vr
        iframe
        ipureintro
        rw [Hrnat]
        exact ⟨Hpick.1 vr rfl (by word), by word⟩
      · wp_join_done
        iexists _, vl
        iframe
        ipureintro
        rw [Hlnat]
        refine ⟨Hpick.2 ?_, by word⟩
        intro v hv; cases hv; omega
    · wp_join_done
      iexists _, vl
      iframe
      ipureintro
      have Hnone : ys[2 * sint.nat i + 2]? = none := by
        rw [List.getElem?_eq_none_iff]; word
      rw [Hlnat]
      refine ⟨(minChild_pick Hvl_lookup none Hnone).2 (fun v hv => by cases hv), by word⟩
  simp only [named]
  obtain ⟨Hmc, Hc0⟩ := Hc
  have Hcl := lookup_lt Hmc.2.1
  have Hib : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s2.len := by
    rw [Hs2len]; constructor <;> word
  have Hcb : 0 ≤ sint.Z c ∧ sint.Z c < sint.Z s2.len := by
    rw [Hs2len]; constructor <;> word
  list_elem ys (sint.nat i) as vi
  try simp only [Hib, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index s2 _ ys _ vi Hib.1 $$ [Hs] as Hs
  · iframe; ipureintro; exact Hvi_lookup
  (try wp_auto)
  try simp only [Hcb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index s2 _ ys _ vc Hcb.1 $$ [Hs] as Hs
  · iframe; ipureintro; exact Hmc.2.1
  wp_if_destruct
  · -- `s[i] <= s[c]`: done
    wp_for_post
    iapply HΦ
    iexists s2, ys
    iframe
    ipureintro
    exact ⟨Ht_lookup, Hmin, siftDown_done_le Hinv Hmc Hvi_lookup (by word), Hperm⟩
  · -- swap `s[i]` and `s[c]`, go down to `c`
    try simp only [Hib, _root_.and_self, ite_true]
    (try wp_auto)
    try simp only [Hcb, _root_.and_self, ite_true]
    (try wp_auto)
    try simp only [Hcb, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index s2 _ ys _ vc Hcb.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hmc.2.1
    (try wp_auto)
    try simp only [Hib, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index s2 _ ys _ vi Hib.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hvi_lookup
    (try wp_auto)
    wp_apply wp_store_slice_index s2 _ ys vc $$ [Hs] as Hs
    · iframe; ipureintro; exact ⟨Hib.1, by word⟩
    (try wp_auto)
    wp_apply wp_store_slice_index s2 _ _ vi $$ [Hs] as Hs
    · iframe; ipureintro; exact ⟨Hcb.1, by simp only [List.length_set]; word⟩
    (try wp_auto)
    wp_for_post
    iframe
    ipureintro
    have hlt : uint.Z vc < uint.Z vi := by omega
    have Hstep := siftDown_step Hinv Hmc Hvi_lookup hlt
    refine ⟨Hc0, by omega, ?_, ?_, ?_⟩
    · exact Hstep
    · exact (List.Perm.cons t (swap_perm ys _ _ vi vc Hvi_lookup Hmc.2.1)).trans Hperm
    · simp only [List.length_set]; exact HyL

end proof

end EtcdGrove
end Perennial
