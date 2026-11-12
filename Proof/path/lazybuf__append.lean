/-
Proof of `Spec/path/lazybuf__append.lean`. Lean-first.
-/
module

public import Spec.path.lazybuf__append

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.path.Assumptions]

theorem path.lazybuf.append.wp_proof : path.lazybuf.append.spec (GF := GF) (hG := hG) := by
  intro b p P w c Hw
  wp_start as Hb
  iunfold path.lbOwn at Hb
  icases Hb with ⟨%buf, Hs, Hbuf, Hwf, %Hwb, Hcase⟩
  try wp_auto
  icases Hcase with (⟨%Hnil, %HP⟩ | ⟨⟨%Hnn, %HPl⟩, Hsl⟩)
  · subst Hnil HP
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    try wp_auto
    have hlt : sint.Z (W64 (w : Int)) < sint.Z (W64 (P.length : Int)) := by word
    have hw1 : sint.nat (W64 (w : Int)) = w := by word
    have hw0 : 0 ≤ sint.Z (W64 (w : Int)) := by word
    obtain ⟨v, hv⟩ : ∃ v, P[w]? = some v := ⟨_, List.getElem?_eq_getElem Hw⟩
    simp only [hlt, decide_true, ↓reduceIte]
    try wp_auto
    rw [if_pos hw0, hw1, hv]
    try wp_auto
    by_cases hvc : v = c
    · -- the path's byte: `w` moves on
      subst hvc
      simp only [decide_true]
      try wp_auto
      iapply HΦ
      iexists P
      isplitl
      · iunfold path.lbOwn
        iexists slice.nil
        iframe
        isplitl [Hwf]
        · rw [show W64 ((w + 1 : Nat) : Int) = W64 (w : Int) + W64 1 by word]
          iexact Hwf
        isplitr
        · ipureintro; omega
        ileft; ipureintro; exact ⟨rfl, rfl⟩
      ipureintro
      refine ⟨by rw [List.take_succ, hv]; rfl, rfl⟩
    · simp only [decide_eq_false hvc]
      try wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      wp_apply (wp_slice_make2 (V := w8) (W64 (P.length : Int))) as %sl ⟨Hsl, -⟩
      · ipureintro; word
      try wp_auto
      rw [if_pos (by refine ⟨by word, by word, by word⟩)]
      try wp_auto
      simp only [hw1, show sint.nat (W64 0) = 0 by rfl, Nat.sub_zero, List.drop_zero]
      wp_apply wp_string_to_bytes (P.take w) as %src ⟨Hsrc, -⟩
      wp_apply wp_slice_copy sl _ src _ _ $$ [$Hsl $Hsrc] as %n ⟨-, Hsl, -⟩
      try wp_auto
      ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
      have hPn : sint.nat (W64 (P.length : Int)) = P.length := by word
      simp only [hPn, List.length_replicate, List.length_take] at Hlen ⊢
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by
        simp only [List.length_append, List.length_take, List.length_drop, List.length_replicate] at Hlen
        word⟩)]
      wp_apply wp_store_slice_index sl (sint.Z (W64 (w : Int))) _ c $$ [Hsl] as Hsl
      · iframe; ipureintro
        simp only [List.length_append, List.length_take, List.length_drop, List.length_replicate]
        constructor <;> word
      try wp_auto
      have hw : (sint.Z (W64 (w : Int))).toNat = w := by word
      rw [hw]
      iapply HΦ
      iexists _
      have hL : (List.take P.length (List.take w P) ++
          List.drop (min w P.length) (List.replicate P.length (zero_val w8))).length = P.length := by
        simp; omega
      have hnn : sl ≠ slice.nil := by
        intro h
        have h1 := Hlen.1
        rw [hL, h] at h1
        simp [slice.nil] at h1
        have hz : sint.nat (0#64 : w64) = 0 := rfl
        omega
      isplitl
      · iunfold path.lbOwn
        iexists sl
        iframe
        isplitl [Hwf]
        · rw [show W64 ((w + 1 : Nat) : Int) = W64 (w : Int) + W64 1 by word]
          iexact Hwf
        isplitr
        · ipureintro; omega
        iright; iframe; ipureintro
        exact ⟨hnn, by rw [List.length_set]; exact hL⟩
      ipureintro
      refine ⟨?_, by rw [List.length_set]; exact hL⟩
      rw [path.take_set_succ _ w c (by rw [hL]; exact Hw)]
      have h1 : min P.length w = w := by omega
      have h2 : min w P.length = w := by omega
      simp [List.take_append, List.take_take, h1, h2]
  · ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    simp only [Hnn, decide_false]
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    wp_apply wp_store_slice_index buf (sint.Z (W64 (w : Int))) P c $$ [Hsl] as Hsl
    · iframe; ipureintro; constructor <;> word
    try wp_auto
    have hw : (sint.Z (W64 (w : Int))).toNat = w := by word
    rw [hw]
    iapply HΦ
    iexists P.set w c
    isplitl
    · iunfold path.lbOwn
      iexists buf
      iframe
      isplitl [Hwf]
      · rw [show W64 ((w + 1 : Nat) : Int) = W64 (w : Int) + W64 1 by word]
        iexact Hwf
      isplitr
      · ipureintro; omega
      iright; iframe; ipureintro; exact ⟨Hnn, by simp [HPl]⟩
    ipureintro
    exact ⟨path.take_set_succ P w c (by omega), by simp [HPl]⟩

end proof

end EtcdGrove
end Perennial
