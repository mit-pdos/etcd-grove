/-
Proof of `Spec/google_golang_org/grpc/internal/mem/compactExponents.lean` (grpc-mem, 2026-11-26).
-/
module

public import Spec.google_golang_org.grpc.internal.mem.compactExponents

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.internal.mem.Assumptions]

theorem grpc.internal.mem.compactExponents.wp_proof :
    grpc.internal.mem.compactExponents.spec (GF := GF) (hG := hG) := by
  intro s xs
  wp_start as Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_if_destruct
  · -- `len(s) < 2`: `s` itself
    iapply HΦ
    iframe Hs
    ipureintro; intro y hy; exact hy
  -- the first loop: `vs[:k]` holds elements of `xs`, `vs[i:]` is `xs[i:]`
  ihave IH : iprop(∃ (i k : w64) (vs : List w8), "i" ∷ i_ptr ↦ i ∗ "k" ∷ k_ptr ↦ k ∗
      "s" ∷ s_ptr ↦ s ∗ "Hs" ∷ s ↦* vs ∗
      "%Hinv" ∷ ⌜vs.length = xs.length ∧ 1 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z i ∧
        sint.Z i ≤ xs.length ∧ (∀ j y, j < sint.nat k → vs[j]? = some y → y ∈ xs) ∧
        (∀ j, sint.nat i ≤ j → vs[j]? = xs[j]?)⌝) $$ [i k s Hs]
  · iexists (W64 1), (W64 1), xs
    iframe
    ipureintro
    refine ⟨rfl, by word, by word, by word, ?_, fun j _ => rfl⟩
    intro j y _ hy; exact List.mem_of_getElem? hy
  wp_for IH
  wp_if_destruct
  · ihave %Hsl := ownSlice_len _ _ _ $$ Hs
    obtain ⟨Hvl, Hk1, Hki, Hil, Hpre, Hsuf⟩ := Hinv
    have Hif' : sint.Z i < sint.Z s.len := by simpa using Hif
    have hi0 : 0 ≤ sint.Z i := by word
    have hk0 : 0 ≤ sint.Z (k - W64 1) := by word
    have hkl : sint.Z (k - W64 1) < sint.Z s.len := by word
    obtain ⟨xi, Hxi⟩ : ∃ y, xs[sint.nat i]? = some y :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have Hvi : vs[sint.nat i]? = some xi := by rw [Hsuf _ (Nat.le_refl _)]; exact Hxi
    obtain ⟨yk, Hyk⟩ : ∃ y, vs[sint.nat (k - W64 1)]? = some y :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    rw [ite_eq_left ⟨hi0, Hif'⟩]
    wp_apply wp_load_slice_index s (sint.Z i) vs (DFrac.own 1) xi hi0 $$ [Hs] as Hs
    · iframe Hs; ipureintro; exact Hvi
    try wp_auto
    rw [ite_eq_left ⟨hk0, hkl⟩]
    wp_apply wp_load_slice_index s (sint.Z (k - W64 1)) vs (DFrac.own 1) yk hk0 $$ [Hs] as Hs
    · iframe Hs; ipureintro; exact Hyk
    try wp_auto
    have hkk : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z s.len := ⟨by word, by word⟩
    wp_if_destruct
    · -- `s[i] == s[k-1]`: nothing
      wp_for_post
      iframe
      iexists (i + W64 1), k, vs
      iframe
      ipureintro
      exact ⟨Hvl, Hk1, by word, by word, Hpre, fun j hj => Hsuf j (by word)⟩
    · -- `s[i] != s[k-1]`: `s[k] = s[i]; k++`
      try wp_auto
      rw [ite_eq_left ⟨hi0, Hif'⟩]
      wp_apply wp_load_slice_index s (sint.Z i) vs (DFrac.own 1) xi hi0 $$ [Hs] as Hs
      · iframe Hs; ipureintro; exact Hvi
      try wp_auto
      rw [ite_eq_left hkk]
      wp_apply wp_store_slice_index s (sint.Z k) vs xi $$ [Hs] as Hs
      · iframe Hs; ipureintro; exact ⟨hkk.1, by word⟩
      try wp_auto
      wp_for_post
      iframe
      iexists (i + W64 1), (k + W64 1), (vs.set (sint.Z k).toNat xi)
      iframe
      ipureintro
      have hkn : (sint.Z k).toNat = sint.nat k := rfl
      refine ⟨by rw [List.length_set]; exact Hvl, by word, by word, by word, ?_, ?_⟩
      · intro j y hj hy
        rw [hkn] at hy
        by_cases hjk : j = sint.nat k
        · subst hjk
          rw [List.getElem?_set_self (by word)] at hy
          cases hy; exact List.mem_of_getElem? Hxi
        · rw [List.getElem?_set_ne (Ne.symm hjk)] at hy
          exact Hpre j y (by word) hy
      · intro j hj
        rw [hkn, List.getElem?_set_ne (by word)]
        exact Hsuf j (by word)
  · -- the second loop: zero the tail `s[k:]`
    obtain ⟨Hvl, Hk1, Hki, Hil, Hpre, Hsuf⟩ := Hinv
    ihave %Hsl := ownSlice_len _ _ _ $$ Hs
    have Hif' : ¬ sint.Z i < sint.Z s.len := by simpa using Hif
    ihave IH2 : iprop(∃ (jj : w64) (ws : List w8), "j" ∷ j_ptr ↦ jj ∗ "s" ∷ s_ptr ↦ s ∗
        "Hs" ∷ s ↦* ws ∗
        "%Hinv2" ∷ ⌜ws.length = xs.length ∧ sint.Z k ≤ sint.Z jj ∧
          (∀ j y, j < sint.nat k → ws[j]? = some y → y ∈ xs)⌝) $$ [j s Hs]
    · iexists k, vs
      iframe
      ipureintro
      exact ⟨Hvl, Int.le_refl _, Hpre⟩
    wp_for IH2
    wp_if_destruct
    · obtain ⟨Hwl, Hkj, Hpre2⟩ := Hinv2
      ihave %Hsl2 := ownSlice_len _ _ _ $$ Hs
      have Hif2 : sint.Z jj < sint.Z s.len := Hif
      have hjj : 0 ≤ sint.Z jj ∧ sint.Z jj < sint.Z s.len := ⟨by word, Hif2⟩
      try wp_auto
      rw [ite_eq_left hjj]
      wp_apply wp_store_slice_index s (sint.Z jj) ws (W8 0) $$ [Hs] as Hs
      · iframe Hs; ipureintro; exact ⟨hjj.1, by word⟩
      try wp_auto
      wp_for_post
      iframe
      iexists (jj + W64 1), (ws.set (sint.Z jj).toNat (W8 0))
      iframe
      ipureintro
      refine ⟨by rw [List.length_set]; exact Hwl, by word, ?_⟩
      intro j y hj hy
      rw [List.getElem?_set_ne (by word)] at hy
      exact Hpre2 j y hj hy
    · -- `return s[:k]`
      obtain ⟨Hwl, Hkj, Hpre2⟩ := Hinv2
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
      have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z k ∧ sint.Z k ≤ sint.Z s.cap :=
        ⟨by word, by word, by word⟩
      try wp_auto
      rw [ite_eq_left hb]
      try wp_auto
      icases (ownSlice_slice (W64 0) k s (DFrac.own 1) ws ⟨by word, by word, by word⟩).1 $$ Hs
        with ⟨Hs0, Hsk, -⟩
      iapply HΦ
      iframe Hsk
      ipureintro
      intro y hy
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hy
      simp only [subslice, show sint.nat (W64 0) = 0 from rfl, List.drop_zero,
        List.getElem?_take] at hj
      split at hj
      · exact Hpre2 j y (by assumption) hj
      · cases hj

end proof

end EtcdGrove
end Perennial
