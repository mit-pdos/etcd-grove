/-
The proof of `Spec/go_etcd_io/bbolt/DB__needsInit.lean` (U11 of `notes/bbolt-proof-plan.md`; until
the fork's 2026-11-25 port of the etcd fork's recovery, `Open/MetasZero.lean`'s `metasZero`): the
file's bytes read whole, then compared byte by byte with `initImage`'s.
-/
module

public import Spec.go_etcd_io.bbolt.DB__needsInit
public import Perennial.Proof.io

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.needsInit.wp_proof
    (hRead : os.File.ReadAt.specRacyLt (GF := GF) (hG := hG))
    (hImage : DB.initImage.spec (GF := GF) (hG := hG)) :
    DB.needsInit.spec (GF := GF) (hG := hG) := by
  intro db f fd p dqdb dqf dq dqb d ro xs hrd hp hx
  rcases p with ⟨pp, pi, pcs⟩; dsimp only at hp ⊢; subst hp
  wp_start as ⟨#Hos, Hf, Hps, Hro, Hfo, Hfd, Hb⟩
  by_cases h0 : xs.length = 0
  · rw [h0]
    wp_auto
    iapply HΦ
    iframe Hf Hps Hro Hfo Hfd Hb
    ileft; ipureintro; exact ⟨rfl, fun _ => rfl, fun _ => Or.inl rfl⟩
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hn := io.eof_of_init $$ Hio
  isimp only [_root_.Perennial.errors.newVar] at Hn
  icases Hn with ⟨%eofl, #Heof, -⟩
  have hn : W64 (xs.length : Int) ≠ W64 0 := by word
  try wp_auto
  rw [decide_eq_false hn]
  try wp_auto
  cases ro
  rotate_left
  · -- read-only: only an empty file is initialized
    try wp_auto
    iapply HΦ
    iframe Hf Hps Hro Hfo Hfd Hb
    ileft; ipureintro; exact ⟨rfl, fun h => absurd h h0, fun h => nomatch h⟩
  try wp_auto
  wp_if_destruct
  · -- more than four pages
    try wp_auto
    iapply HΦ
    iframe Hf Hps Hro Hfo Hfd Hb
    ileft; ipureintro; exact ⟨rfl, fun h => absurd h h0, fun h => nomatch h⟩
  have hle : xs.length ≤ 16384 := by
    have := Hif
    first
      | (rw [show W64 4096 * W64 4 = W64 16384 from rfl] at this; word)
      | word
  clear Hif
  try wp_auto
  -- the file's bytes
  wp_apply wp_slice_make2 (V := w8) (W64 (xs.length : Int)) as %sl ⟨Hsl, -⟩
  · ipureintro; word
  have hsn : sint.nat (W64 (xs.length : Int)) = xs.length := by word
  rw [hsn]
  try wp_auto
  wp_apply os.File.ReadAt.wp_heldW hRead f fd pp dqf sl (List.replicate xs.length (W8 0)) (W64 0) dq
    dqb d xs _ hrd (by decide) (by rw [List.length_replicate]; omega)
    (by rw [List.length_replicate, show (W64 0).toNat = 0 from rfl]; omega) (by omega)
    $$ [Hfo Hsl Hfd Hb] as %n %err ⟨Hfo, Hfd, Hb, %vs', Hsl, %hr, #Hek⟩
  · iframe; iframe #; rw [← fileOwn_eq]; iexact Hfo
  rw [List.length_replicate, show (W64 0).toNat = 0 from rfl, List.drop_zero] at hr
  rcases hr with ⟨rfl, rfl, rfl⟩ | ⟨pe, rfl, hne⟩
  rotate_left
  · -- a read error
    wp_auto
    iapply HΦ
    rw [fileOwn_eq]
    iframe Hf Hps Hro Hfo Hfd Hb
    iright
    isplitr
    · ipureintro; exact ⟨(fun h => by cases h), hne⟩
    · iapply fmtErrorOkOrNil_ne (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)
        (by intro h; cases h) $$ Hek
  have htk : List.take xs.length (List.map Prod.fst xs) = List.map Prod.fst xs :=
    List.take_of_length_le (by simp)
  rw [htk]
  wp_auto
  -- the image `init` writes
  wp_apply hImage db dqdb $$ [Hps] as %im ⟨Hps, Him, -⟩
  · iframe Hps; try iframe #
  -- `initImg` as a variable, so that no unification in the loop unfolds it
  have hIl : initImg.length = 16384 := initImg_length
  generalize hI : initImg = I at hIl ⊢
  have hBl : (List.map Prod.fst xs).length = xs.length := by simp
  generalize hB : List.map Prod.fst xs = B at hBl ⊢
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  ihave %Himl := ownSlice_len _ _ _ $$ Him
  have hsl : sint.Z sl.len = (xs.length : Int) := by
    have := Hsll.1; rw [hBl] at this; have := Hsll.2; word
  have him : sint.Z im.len = 16384 := by
    have := Himl.1; rw [hIl] at this; have := Himl.2; word
  try wp_auto
  -- the comparison
  ihave IH : (∃ (k : Nat) (bv : w8) (jv : w64) (wv : Bool),
      "i" ∷ i_ptr ↦ W64 (k : Int) ∗ "b" ∷ b_ptr ↦ bv ∗ "j" ∷ j_ptr ↦ jv ∗
      "whole" ∷ whole_ptr ↦ wv ∗
      "%Hk" ∷ ⌜k ≤ xs.length ∧ ∀ (i : Nat) (c : w8), i < k → B[i]? = some c →
        c = W8 0 ∨ I[i]? = some c⌝ ∗
      "Hsl" ∷ sl ↦* B ∗ "Him" ∷ im ↦* I : IProp GF) $$ [i b j whole Hsl Him]
  · iexists 0, _, _, _
    simp only [named]
    iframe i b j whole Hsl Him
    ipureintro
    exact ⟨Nat.zero_le _, fun i _ h => absurd h (Nat.not_lt_zero _)⟩
  wp_for IH
  have hkZ : sint.Z (W64 (k : Int)) = (k : Int) := by word
  rw [hsl, hkZ]
  by_cases hlt : (k : Int) < xs.length
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    wp_auto
    rw [hkZ, hsl, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, hlt⟩)]
    obtain ⟨bk, hbk⟩ : ∃ bk, B[k]? = some bk :=
      ⟨B[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨ik, hik⟩ : ∃ ik, I[k]? = some ik :=
      ⟨I[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    icases ownSlice_elem_acc (k : Int) bk sl _ B (by omega) (by simpa using hbk) $$ Hsl
      with ⟨He, Hsl⟩
    wp_auto
    ihave Hsl := Hsl $$ He
    try rw [show (k : Int).toNat = k from rfl]
    rw [list_set_lookup_self B k bk hbk]
    rw [hkZ, him, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
    icases ownSlice_elem_acc (k : Int) ik im _ I (by omega) (by simpa using hik) $$ Him
      with ⟨Hie, Him⟩
    wp_auto
    ihave Him := Him $$ Hie
    try rw [show (k : Int).toNat = k from rfl]
    rw [list_set_lookup_self I k ik hik]
    have hstep : ∀ (i : Nat) (c : w8), i < k + 1 → B[i]? = some c →
        (bk = ik ∨ bk = W8 0) → c = W8 0 ∨ I[i]? = some c := by
      intro i c hi hc hbe
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact Hk.2 i c h hc
      · subst h
        rw [hbk] at hc
        cases hc
        rcases hbe with hbe | hbe
        · right; rw [hik, hbe]
        · left; exact hbe
    by_cases he : bk = ik
    · -- the byte is init's
      rw [decide_eq_true he]
      wp_auto
      wp_for_post
      iframe
      iexists k + 1, _, _, _
      simp only [named]
      rw [show W64 ((k + 1 : Nat) : Int) = W64 (k : Int) + W64 1 by word]
      iframe i b j whole Hsl Him
      ipureintro
      exact ⟨by omega, fun i c hi hc => hstep i c hi hc (Or.inl he)⟩
    · rw [decide_eq_false he]
      wp_auto
      by_cases hz : bk = W8 0
      · -- a zero byte (not written yet)
        rw [decide_eq_true hz]
        wp_auto
        wp_for_post
        iframe
        iexists k + 1, _, _, _
        simp only [named]
        rw [show W64 ((k + 1 : Nat) : Int) = W64 (k : Int) + W64 1 by word]
        iframe i b j whole Hsl Him
        ipureintro
        exact ⟨by omega, fun i c hi hc => hstep i c hi hc (Or.inr hz)⟩
      · -- a byte `init` does not write: not an interrupted `init`
        rw [decide_eq_false hz]
        wp_auto
        iapply wp_for_post_return
        wp_auto
        iapply HΦ
        rw [fileOwn_eq]
        iframe Hf Hps Hro Hfo Hfd Hb
        ileft
        ipureintro
        exact ⟨rfl, fun h => absurd h h0, fun h => nomatch h⟩
  · simp only [hlt, _root_.decide_false, intoVal_eq_iff, Bool.false_eq_true, ↓reduceIte,
      decide_eq_true_eq]
    wp_auto
    iapply HΦ
    rw [fileOwn_eq]
    iframe Hf Hps Hro Hfo Hfd Hb
    ileft
    ipureintro
    refine ⟨rfl, fun h => absurd h h0, fun _ => Or.inr ⟨by omega, fun i c hc => ?_⟩⟩
    have hi : i < B.length := by
      rcases Nat.lt_or_ge i B.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hc
        cases hc
    rw [hI]
    exact Hk.2 i c (by omega) hc

end proof

end bbolt
end EtcdGrove
end Perennial
