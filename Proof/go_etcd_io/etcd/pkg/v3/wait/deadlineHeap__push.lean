/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/wait/deadlineHeap__push.lean`. Lean-first (no Rocq
counterpart; pr-verify/etcd-22495, 2026-10-17).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.deadlineHeap__push
public import Proof.go_etcd_io.etcd.pkg.v3.wait.HeapAppend

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

/-- Go's signed `x / 2` of a non-negative `x` (Perennial's `slices.sdiv2_nonneg`). -/
theorem sdiv2_nonneg' (x : w64) (h : 0 ≤ sint.Z x) : BitVec.sdiv x (W64 2) = x / (2 : w64) := by
  have hmsb : x.msb = false := by
    rw [BitVec.msb_eq_toInt]; simp only [decide_eq_false_iff_not]; simp only [sint.Z] at h; omega
  rw [BitVec.sdiv_eq, hmsb]
  rfl

theorem wait.deadlineHeap.push.wp_proof : wait.deadlineHeap.push.spec (GF := GF) (hG := hG) := by
  intro hp s xs d
  wp_start as ⟨Hh, Hs, Hcap, %Hheap⟩
  wp_auto
  wp_apply wp_slice_literal (V := w64) [d]
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  wp_auto
  wp_apply wait.deadlineHeap.append_len_bound $$ [$Hs $Hcap $Hsl2] as %s1 ⟨Hs, Hcap, -, %Hlen⟩
  (try wp_auto)
  ihave %Hl1 := ownSlice_len _ _ _ $$ Hs
  simp only [List.length_append, List.length_singleton] at Hlen Hl1
  ihave HI : (∃ (i : w64) (ys : List w64), "i" ∷ i_ptr ↦ i ∗ "Hs" ∷ s1 ↦* ys ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i < sint.Z s1.len ∧ siftUpInv ys (sint.nat i) ∧
        ys ≡ₚ xs ++ [d] ∧ ys.length = xs.length + 1⌝ : IProp GF) $$ [i Hs]
  · iexists s1.len - W64 1, xs ++ [d]
    iframe
    ipureintro
    have hn : sint.nat (s1.len - W64 1) = xs.length := by word
    refine ⟨by word, by word, ?_, List.Perm.refl _, by simp⟩
    rw [hn]; exact siftUp_init Hheap d
  wp_for HI
  wp_if_destruct
  · obtain ⟨Hi0, HiL, Hinv, Hperm, HyL⟩ := Hi
    rw [sdiv2_nonneg' _ (by word)]
    have Hpz : sint.Z ((i - W64 1) / (2 : w64)) = (sint.Z i - 1) / 2 := by word
    have Hpn : sint.nat ((i - W64 1) / (2 : w64)) = (sint.nat i - 1) / 2 := by word
    have Hpb : 0 ≤ sint.Z ((i - W64 1) / (2 : w64)) ∧ sint.Z ((i - W64 1) / (2 : w64)) < sint.Z s1.len := by
      constructor <;> word
    have Hib : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s1.len := ⟨Hi0, HiL⟩
    simp only [Hpb, _root_.and_self, ↓reduceIte]
    list_elem ys (sint.nat ((i - W64 1) / (2 : w64))) as a
    list_elem ys (sint.nat i) as b
    wp_apply wp_load_slice_index s1 _ ys _ a Hpb.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Ha_lookup
    simp only [Hib, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index s1 _ ys _ b Hi0 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hb_lookup
    wp_if_destruct
    · -- `s[p] <= s[i]`: done
      wp_for_post
      iapply HΦ
      iexists s1, ys
      iframe
      ipureintro
      rw [Hpn] at Ha_lookup
      exact ⟨siftUp_done_le Hinv Ha_lookup Hb_lookup (by word), Hperm, by omega⟩
    · -- swap `s[p]` and `s[i]`, go up to `p`
      have hpl : sint.nat ((i - W64 1) / 2) < ys.length := by word
      have hil : sint.nat i < ys.length := by word
      try simp only [Hpb, _root_.and_self, ite_true]
      (try wp_auto)
      try simp only [Hib, _root_.and_self, ite_true]
      (try wp_auto)
      try simp only [Hib, _root_.and_self, ite_true]
      wp_apply wp_load_slice_index s1 _ ys _ b Hi0 $$ [Hs] as Hs
      · iframe; ipureintro; exact Hb_lookup
      (try wp_auto)
      try simp only [Hpb, _root_.and_self, ite_true]
      wp_apply wp_load_slice_index s1 _ ys _ a Hpb.1 $$ [Hs] as Hs
      · iframe; ipureintro; exact Ha_lookup
      (try wp_auto)
      wp_apply wp_store_slice_index s1 _ ys b $$ [Hs] as Hs
      · iframe; ipureintro; exact ⟨Hpb.1, by word⟩
      (try wp_auto)
      wp_apply wp_store_slice_index s1 _ _ a $$ [Hs] as Hs
      · iframe; ipureintro; exact ⟨Hi0, by simp only [List.length_set]; word⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists (i - W64 1) / 2, _
      iframe
      ipureintro
      have hlt : uint.Z b < uint.Z a := by omega
      rw [Hpn] at Ha_lookup hpl ⊢
      have Hstep := siftUp_step Hinv (by word) Ha_lookup Hb_lookup hlt
      refine ⟨Hpb.1, Hpb.2, ?_, ?_, ?_⟩
      · rw [show (sint.Z ((i - W64 1) / 2)).toNat = (sint.nat i - 1) / 2 from Hpn,
          show (sint.Z i).toNat = sint.nat i from rfl]
        exact Hstep
      · rw [show (sint.Z ((i - W64 1) / 2)).toNat = (sint.nat i - 1) / 2 from Hpn,
          show (sint.Z i).toNat = sint.nat i from rfl]
        exact (swap_perm ys _ _ a b Ha_lookup Hb_lookup).trans Hperm
      · simp only [List.length_set]; exact HyL

  · iapply HΦ
    iexists s1, ys
    iframe
    ipureintro
    obtain ⟨_, _, Hinv, Hperm, HyL⟩ := Hi
    have h0 : sint.nat i = 0 := by word
    rw [h0] at Hinv
    exact ⟨siftUp_done_root Hinv, Hperm, by omega⟩

end proof

end EtcdGrove
end Perennial
