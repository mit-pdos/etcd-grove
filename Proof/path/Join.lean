/-
Proof of `Spec/path/Join.lean`. Lean-first.
-/
module

public import Spec.path.Join
public import Spec.path.Clean

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

set_option hygiene false in
/-- The buffer loop's next round, the buffer `b'` holding the step's result. -/
local macro "jpost" b':term:max : tactic => `(tactic| (
  wp_for_post
  iframe
  iexists n + 1, $b', ei
  rw [show W64 (((n + 1 : Nat) : Int)) = W64 (n : Int) + W64 1 by word, path.joinBuf_take_succ es n hn, hen,
    hstep]
  iframe
  ipureintro; omega))

theorem path.Join.wp_proof (hClean : path.Clean.spec (GF := GF) (hG := hG)) :
    path.Join.spec (GF := GF) (hG := hG) := by
  intro sl es dq Hsum
  wp_start as Hsl
  ihave %Hsll := ownSlice_len $$ Hsl
  try wp_auto
  have Hesl : es.length < 2 ^ 62 := by omega
  ihave HI : (∃ (n : Nat) (ev : GoString), "i" ∷ i_ptr ↦ W64 (n : Int) ∗
      "size" ∷ size_ptr ↦ W64 (((es.take n).map List.length).sum : Int) ∗ "e" ∷ e_ptr ↦ ev ∗
      "%Hn" ∷ ⌜n ≤ es.length⌝ : IProp GF) $$ [i size e]
  · iexists 0, _
    iframe
    ipureintro; omega
  wp_for HI
  have Hn63 : n < 2 ^ 62 := by omega
  by_cases hn : n < es.length
  · have hc : sint.Z (W64 (n : Int)) < sint.Z sl.len := by
      have := Hsll.1; word
    rw [if_pos (decide_eq_true hc)]
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, hc⟩)]
    obtain ⟨ei, hei⟩ : ∃ e, es[n]? = some e := ⟨_, List.getElem?_eq_getElem hn⟩
    wp_apply wp_load_slice_index sl (sint.Z (W64 (n : Int))) es dq ei (by word) $$ [Hsl] as Hsl
    · iframe; ipureintro; rw [show (sint.Z (W64 (n : Int))).toNat = n by word]; exact hei
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    try wp_auto
    wp_for_post
    iframe
    iexists n + 1, ei
    have hsum : ((es.take (n + 1)).map List.length).sum = ((es.take n).map List.length).sum + ei.length := by
      rw [List.take_succ, hei]; simp
    rw [hsum, show W64 (((n + 1 : Nat) : Int)) = W64 (n : Int) + W64 1 by word,
      show W64 ((((es.take n).map List.length).sum + ei.length : Nat) : Int) =
        W64 ((((es.take n).map List.length).sum : Nat) : Int) + W64 (ei.length : Int) by word]
    iframe
    ipureintro; omega
  · have hne : n = es.length := by omega
    subst hne
    have hc : ¬ sint.Z (W64 (es.length : Int)) < sint.Z sl.len := by
      have := Hsll.1; word
    rw [if_neg (by rw [decide_eq_true_eq]; exact hc)]
    rw [if_neg (by rw [decide_eq_true_eq]; exact hc)]
    rw [List.take_length]
    try wp_auto
    have HS : (es.map List.length).sum < 2 ^ 62 := by omega
    by_cases hS : (es.map List.length).sum = 0
    · rw [hS]
      try wp_auto
      iapply HΦ
      iframe
      ipureintro
      simp [path.joinModel, hS]
    · have hS' : W64 (((es.map List.length).sum : Nat) : Int) ≠ W64 0 := by intro h; apply hS; word
      simp only [hS', decide_false]
      try wp_auto
      have hcap : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤
          sint.Z (W64 (((es.map List.length).sum : Nat) : Int) + sl.len - W64 1) := by
        have := Hsll.1; have := Hsll.2
        have h1 : 1 ≤ (es.map List.length).sum := by omega
        constructor <;> word
      wp_apply (wp_slice_make3 (V := w8) (W64 0) _ hcap) as %bs ⟨Hbs, Hcap, -⟩
      try wp_auto
      ihave HJ : (∃ (n : Nat) (b : GoSlice) (ev : GoString), "i" ∷ i_ptr ↦ W64 (n : Int) ∗
          "buf" ∷ buf_ptr ↦ b ∗ "Hbs" ∷ b ↦* path.joinBuf (es.take n) [] ∗
          "Hcap" ∷ ownSliceCap w8 b (DFrac.own 1) ∗ "e" ∷ e_ptr ↦ ev ∗ "%Hn" ∷ ⌜n ≤ es.length⌝ :
          IProp GF) $$ [i buf Hbs Hcap e]
      · iexists 0, bs, _
        simp only [show sint.nat (W64 0) = 0 by rfl, List.replicate_zero, List.take_zero]
        iframe
        ipureintro; omega
      wp_for HJ
      have Hn63 : n < 2 ^ 62 := by omega
      by_cases hn : n < es.length
      · have hc : sint.Z (W64 (n : Int)) < sint.Z sl.len := by
          have := Hsll.1; word
        rw [if_pos (decide_eq_true hc)]
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, hc⟩)]
        obtain ⟨ei, hei⟩ : ∃ e, es[n]? = some e := ⟨_, List.getElem?_eq_getElem hn⟩
        wp_apply wp_load_slice_index sl (sint.Z (W64 (n : Int))) es dq ei (by word) $$ [Hsl] as Hsl
        · iframe; ipureintro; rw [show (sint.Z (W64 (n : Int))).toNat = n by word]; exact hei
        try wp_auto
        ihave %Hbl := ownSlice_len $$ Hbs
        have hen : es[n]'hn = ei := by
          rw [List.getElem?_eq_getElem hn] at hei; exact Option.some.inj hei
        by_cases hB : 0 < (path.joinBuf (es.take n) []).length
        · have hbl : sint.Z (W64 0) < sint.Z b.len := by have := Hbl.1; word
          simp only [hbl, _root_.decide_true]
          try wp_auto
          simp only [hbl, _root_.decide_true]
          try wp_auto
          wp_apply wp_slice_literal (V := w8) [W8 47]
          isplitr
          · ipureintro; rfl
          iintro %lit ⟨Hlit, -⟩
          wp_apply wp_slice_append b _ _ _ _ $$ [$Hbs $Hcap $Hlit] as %b1 ⟨Hbs, Hcap, -⟩
          try wp_auto
          wp_apply wp_string_to_bytes ei as %eb ⟨Heb, -⟩
          wp_apply wp_slice_append b1 _ eb _ _ $$ [$Hbs $Hcap $Heb] as %b2 ⟨Hbs, Hcap, -⟩
          try wp_auto
          have hstep : path.joinStep (path.joinBuf (es.take n) []) ei =
              path.joinBuf (es.take n) [] ++ [W8 47] ++ ei := by
            simp [path.joinStep, hB, path.slash]
          jpost b2
        · have hB0 : path.joinBuf (es.take n) [] = [] := by
            cases h : path.joinBuf (es.take n) [] with
            | nil => rfl
            | cons _ _ => rw [h] at hB; simp at hB
          have hbl : ¬ sint.Z (W64 0) < sint.Z b.len := by have := Hbl.1; rw [hB0] at this; word
          simp only [hbl, _root_.decide_false]
          try wp_auto
          by_cases he : ei = []
          · subst he
            simp only [_root_.decide_true, Bool.not_true]
            try wp_auto
            have hstep : path.joinStep (path.joinBuf (es.take n) []) [] = path.joinBuf (es.take n) [] := by
              simp [path.joinStep, hB0]
            wp_for_post
            iframe
            iexists n + 1, b, []
            rw [show W64 (((n + 1 : Nat) : Int)) = W64 (n : Int) + W64 1 by word,
              path.joinBuf_take_succ es n hn, hen, hstep]
            iframe
            ipureintro; omega
          · simp only [he, _root_.decide_false, Bool.not_false]
            try wp_auto
            simp only [hbl, _root_.decide_false]
            try wp_auto
            wp_apply wp_string_to_bytes ei as %eb ⟨Heb, -⟩
            wp_apply wp_slice_append b _ eb _ _ $$ [$Hbs $Hcap $Heb] as %b2 ⟨Hbs, Hcap, -⟩
            try wp_auto
            have hstep : path.joinStep (path.joinBuf (es.take n) []) ei =
                path.joinBuf (es.take n) [] ++ ei := by
              simp [path.joinStep, hB0, he]
            jpost b2
      · have hne : n = es.length := by omega
        subst hne
        have hc : ¬ sint.Z (W64 (es.length : Int)) < sint.Z sl.len := by
          have := Hsll.1; word
        rw [if_neg (by rw [decide_eq_true_eq]; exact hc)]
        rw [if_neg (by rw [decide_eq_true_eq]; exact hc)]
        rw [List.take_length]
        try wp_auto
        wp_apply wp_bytes_to_string b _ _ $$ Hbs as Hbs
        wp_apply hClean _ as %r %Hr
        try wp_auto
        iapply HΦ
        iframe
        ipureintro
        simp [path.joinModel, hS, Hr]

end proof

end EtcdGrove
end Perennial
