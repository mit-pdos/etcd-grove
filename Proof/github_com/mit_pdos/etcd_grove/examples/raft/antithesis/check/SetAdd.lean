/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `SetAdd`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SetAdd
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.strLess

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem SetAdd_takeWhile_len {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (k : Nat), k ≤ xs.length →
      (∀ j y, j < k → xs[j]? = some y → p y = true) →
      (∀ y, xs[k]? = some y → p y = false) →
      (xs.takeWhile p).length = k := by
  intro xs
  induction xs with
  | nil => intro k hk _ _; simp at hk; simp [hk]
  | cons a t ih =>
    intro k hk hlt hge
    cases k with
    | zero => simp [hge a rfl]
    | succ k =>
      have ha : p a = true := hlt 0 a (by omega) rfl
      simp only [List.takeWhile_cons, ha, ite_true, List.length_cons]
      congr 1
      exact ih k (by simp at hk; omega) (fun j y hj hy => hlt (j + 1) y (by omega) hy) (fun y hy => hge y hy)

theorem SetAdd_mk_bound (sl : GoSlice) (L : Nat) (hL : L = sint.nat sl.len) (h0 : 0 ≤ sint.Z sl.len)
    (h : (L : Int) + 1 < 2 ^ 63) : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (sl.len + W64 1) := by
  have : (L : Int) = sint.Z sl.len := by rw [hL]; word
  constructor <;> word

theorem SetAdd.wp_proof (wp_strLess : strLess.spec (GF := GF) (hG := hG)) :
    SetAdd.spec (GF := GF) (hG := hG) := by
  intro sl xs x
  wp_start as ⟨#Hs, %Hlen⟩
  iunfold strsRO at Hs
  ihave %Hl := ownSlice_len $$ Hs
  iapply wp_fupd
  wp_auto
  ihave IH : iprop(∃ (n : w64),
      "k" ∷ k_ptr ↦ n ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        ∀ j y, j < sint.nat n → xs[j]? = some y → strLess y x = true⌝) $$ [k]
  · iexists _
    iframe
    ipureintro
    refine ⟨by word, by word, fun j y hj _ => by rw [show sint.nat (W64 0) = 0 from rfl] at hj; omega⟩
  wp_for IH
  obtain ⟨hn0, hn1, hnlt⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by rw [Hl.1]; word
    obtain ⟨z, Hz⟩ : ∃ z, xs[sint.nat n]? = some z := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) xs DFrac.discard z hn0 $$ [Hs] as -
    · isplitr
      · iexact Hs
      ipureintro; exact Hz
    try wp_auto
    wp_apply wp_strLess z x
    cases hzx : strLess z x
    · simp only [intoVal_eq_iff, Bool.false_eq_true, decide_False_any, ↓reduceIte,
        decide_True_any]
      try wp_auto
      have hk : (xs.takeWhile (fun y => strLess y x)).length = sint.nat n :=
        SetAdd_takeWhile_len _ xs _ (Nat.le_of_lt Hlt) hnlt (fun y hy => by rw [Hz] at hy; cases hy; exact hzx)
      have hlt0 := Hif
      wp_if_destruct
      rotate_left
      · exfalso; exact Hif hlt0
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, hlt0⟩))]
      wp_apply wp_load_slice_index sl (sint.Z n) xs DFrac.discard z hn0 $$ [Hs] as -
      · isplitr
        · iexact Hs
        ipureintro; exact Hz
      try wp_auto
      wp_if_destruct
      · -- `s[k] == x`: `s` itself
        try wp_auto
        iapply HΦ
        have : setAdd xs x = xs := by
          unfold setAdd; simp only; rw [hk, Hz, Hif]; simp
        rw [this]
        iunfold strsRO
        iexact Hs
      have hnot : xs[sint.nat n]? ≠ some x := by rw [Hz]; intro h; cases h; exact Hif rfl
      try wp_auto
      ihave %Hwf := ownSlice_wf $$ Hs
      have hmk := SetAdd_mk_bound sl xs.length Hl.1 Hl.2 Hlen
      wp_apply wp_slice_make3 (V := Str) (W64 0) (sl.len + W64 1) hmk as %out ⟨Hout, Hcap, -⟩
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z n ∧
        sint.Z n ≤ sint.Z sl.cap from ⟨by word, hn0, Int.le_trans hn1 Hwf.2⟩))]
      try wp_auto
      icases (ownSlice_slice (W64 0) n sl _ xs ⟨by word, hn0, hn1⟩).1 $$ Hs with ⟨-, #H1, -⟩
      wp_apply wp_slice_append out _ _ _ DFrac.discard $$ [Hout Hcap H1] as %s1 ⟨Hs1, Hcap1, -⟩
      · iframe Hout Hcap H1
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [Hs1 Hcap1 Hsl1] as %s2 ⟨Hs2, Hcap2, -⟩
      · iframe
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        sint.Z sl.len ≤ sint.Z sl.cap from ⟨hn0, hn1, Hwf.2⟩))]
      try wp_auto
      icases (ownSlice_slice n sl.len sl _ xs ⟨hn0, hn1, Int.le_refl _⟩).1 $$ Hs with ⟨-, #H2, -⟩
      wp_apply wp_slice_append s2 _ _ _ DFrac.discard $$ [Hs2 Hcap2 H2] as %s3 ⟨Hs3, -, -⟩
      · iframe Hs2 Hcap2 H2
      try wp_auto
      imod ownSlice_persist $$ Hs3 with #Hs3
      imodintro
      iapply HΦ
      iunfold strsRO
      have e : List.replicate 0 (zero_val Str) ++ subslice (sint.nat (W64 0)) (sint.nat n) xs ++ [x] ++
          subslice (sint.nat n) (sint.nat sl.len) xs = setAdd xs x := by
        unfold setAdd
        simp only
        rw [hk, ite_eq_right hnot, show sint.nat (W64 0) = 0 from rfl, ← Hl.1]
        simp [subslice]
      rw [← e]
      iexact Hs3
    · simp only [decide_True_any, ↓reduceIte]
      try wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro j y hj hy
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact hnlt j y h hy
      · subst h; rw [Hz] at hy; cases hy; exact hzx
  · try wp_auto
    have hnx : sint.nat n = xs.length := by rw [Hl.1]; word
    have hk : (xs.takeWhile (fun y => strLess y x)).length = sint.nat n :=
      SetAdd_takeWhile_len _ xs _ (Nat.le_of_eq hnx) hnlt (fun y hy => by
        rw [hnx, List.getElem?_eq_none (Nat.le_refl _)] at hy; cases hy)
    have hnot : xs[sint.nat n]? ≠ some x := by rw [hnx, List.getElem?_eq_none (Nat.le_refl _)]; simp
    rw [decide_eq_false Hif]
    try wp_auto
    ihave %Hwf := ownSlice_wf $$ Hs
    have hmk := SetAdd_mk_bound sl xs.length Hl.1 Hl.2 Hlen
    wp_apply wp_slice_make3 (V := Str) (W64 0) (sl.len + W64 1) hmk as %out ⟨Hout, Hcap, -⟩
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z n ∧
      sint.Z n ≤ sint.Z sl.cap from ⟨by word, hn0, Int.le_trans hn1 Hwf.2⟩))]
    try wp_auto
    icases (ownSlice_slice (W64 0) n sl _ xs ⟨by word, hn0, hn1⟩).1 $$ Hs with ⟨-, #H1, -⟩
    wp_apply wp_slice_append out _ _ _ DFrac.discard $$ [Hout Hcap H1] as %s1 ⟨Hs1, Hcap1, -⟩
    · iframe Hout Hcap H1
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [Hs1 Hcap1 Hsl1] as %s2 ⟨Hs2, Hcap2, -⟩
    · iframe
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
      sint.Z sl.len ≤ sint.Z sl.cap from ⟨hn0, hn1, Hwf.2⟩))]
    try wp_auto
    icases (ownSlice_slice n sl.len sl _ xs ⟨hn0, hn1, Int.le_refl _⟩).1 $$ Hs with ⟨-, #H2, -⟩
    wp_apply wp_slice_append s2 _ _ _ DFrac.discard $$ [Hs2 Hcap2 H2] as %s3 ⟨Hs3, -, -⟩
    · iframe Hs2 Hcap2 H2
    try wp_auto
    imod ownSlice_persist $$ Hs3 with #Hs3
    imodintro
    iapply HΦ
    iunfold strsRO
    have e : List.replicate 0 (zero_val Str) ++ subslice (sint.nat (W64 0)) (sint.nat n) xs ++ [x] ++
        subslice (sint.nat n) (sint.nat sl.len) xs = setAdd xs x := by
      unfold setAdd
      simp only
      rw [hk, ite_eq_right hnot, show sint.nat (W64 0) = 0 from rfl, ← Hl.1]
      simp [subslice]
    rw [← e]
    iexact Hs3

end proof

end AntCheck
end EtcdGrove
end Perennial
