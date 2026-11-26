/- Lean-first (no Rocq counterpart). The proof of `weightsFit`: a loop over the first six weights, summing the positive ones. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.weightsFit

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- The positive parts of the first `k` weights. -/
def posSum (ws : List w64) (k : Nat) : Int := (((ws.map sint.Z).take k).map (fun x => max 0 x)).sum

theorem posSum_succ (ws : List w64) (k : Nat) (v : w64) (h : ws[k]? = some v) :
    posSum ws (k + 1) = posSum ws k + max 0 (sint.Z v) := by
  unfold posSum
  rw [List.take_add_one, List.getElem?_map, h]
  simp

theorem posSum_nonneg (ws : List w64) (k : Nat) : 0 ≤ posSum ws k := by
  unfold posSum
  generalize (ws.map sint.Z).take k = l
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; omega

/-- The loop's end before the sixth weight: `i` is the slice's length. -/
theorem weightsFit_end (j wl : w64) (n : Nat) (hn : n = sint.nat wl) (hj0 : 0 ≤ sint.Z j)
    (hjl : sint.Z j ≤ sint.Z wl) (hc : ¬(sint.Z j < 6 ∧ sint.Z j < sint.Z wl))
    (h6 : sint.Z j < 6) : sint.nat j = n ∧ n ≤ 6 := by
  have hz : sint.Z j = sint.Z wl := by omega
  have hjw : j = wl := BitVec.eq_of_toInt_eq hz
  subst hjw hn
  exact ⟨rfl, by word⟩

theorem weightsFit.wp_proof : weightsFit.spec (GF := GF) (hG := hG) := by
  intro w ws dq
  wp_start as Hw
  ihave %Hwl := ownSlice_len $$ Hw
  wp_auto
  ihave IH : (∃ (j t : w64),
      "i" ∷ i_ptr ↦ j ∗ "total" ∷ total_ptr ↦ t ∗ "w" ∷ w_ptr ↦ w ∗ "Hw" ∷ w ↦*{dq} ws ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 6 ∧ sint.Z j ≤ sint.Z w.len ∧
        sint.Z t = posSum ws (sint.nat j)⌝ : IProp GF)
      $$ [i total w Hw]
  · iexists W64 0, W64 0
    iframe
    ipureintro
    refine ⟨by word, by word, by word, ?_⟩
    unfold posSum; rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for IH
  obtain ⟨hj0, hj6, hjl, ht⟩ := Hj
  have htn := posSum_nonneg ws (sint.nat j)
  by_cases Hc : sint.Z j < 6 ∧ sint.Z j < sint.Z w.len
  · rw [decide_eq_true (show sint.Z j < sint.Z (W64 6) by word)]
    (try wp_auto)
    rw [decide_eq_true Hc.2]
    (try simp only [↓reduceIte, decide_true])
    (try wp_auto)
    have hjl' : sint.nat j < ws.length := by rw [Hwl.1]; word
    list_elem ws (sint.nat j) as wj
    (try simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z w.len from ⟨hj0, Hc.2⟩,
      _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index w (sint.Z j) ws dq wj hj0 $$ [Hw] as Hw
    · iframe; ipureintro; exact Hwj_lookup
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have hs := posSum_succ ws (sint.nat j) wj Hwj_lookup
    wp_if_destruct
    · (try wp_auto)
      (try simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z w.len from ⟨hj0, Hc.2⟩,
        _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index w (sint.Z j) ws dq wj hj0 $$ [Hw] as Hw
      · iframe; ipureintro; exact Hwj_lookup
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_for_post
        iapply HΦ
        iframe
        ipureintro
        intro h; cases h
      · (try wp_auto)
        (try simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z w.len from ⟨hj0, Hc.2⟩,
          _root_.and_self, ↓reduceIte])
        wp_apply wp_load_slice_index w (sint.Z j) ws dq wj hj0 $$ [Hw] as Hw
        · iframe; ipureintro; exact Hwj_lookup
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, t + wj
        iframe
        ipureintro
        refine ⟨by word, by word, by word, ?_⟩
        rw [hj1, hs]
        word
    · (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, t
      iframe
      ipureintro
      refine ⟨by word, by word, by word, ?_⟩
      rw [hj1, hs]
      word
  · -- the loop's end: the sum of the first six (or of all) fits
    have hend : posSum ws (sint.nat j) = posSum ws 6 := by
      unfold posSum
      by_cases h6 : sint.Z j < 6
      · obtain ⟨hjn, hle⟩ := weightsFit_end j w.len ws.length Hwl.1 hj0 hjl Hc h6
        rw [hjn, List.take_of_length_le (by simp), List.take_of_length_le (by simpa using hle)]
      · rw [show sint.nat j = 6 by word]
    have hfit : posSum ws 6 < 2 ^ 63 := by rw [← hend, ← ht]; word
    by_cases h6 : sint.Z j < 6
    · rw [decide_eq_true (show sint.Z j < sint.Z (W64 6) by word)]
      (try wp_auto)
      rw [decide_eq_false (show ¬ sint.Z j < sint.Z w.len by omega)]
      (try simp only [Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
      (try wp_auto)
      (try rw [decide_eq_false (show ¬ ((#false : val) = (#true : val)) by simp [intoVal_eq_iff])])
      (try simp only [Bool.false_eq_true, ↓reduceIte])
      (try wp_auto)
      (try simp only [decide_true, ↓reduceIte])
      (try wp_auto)
      (try simp only [decide_true, ↓reduceIte])
      (try wp_auto)
      iapply HΦ; iframe; ipureintro; intro _; exact hfit
    · rw [decide_eq_false (show ¬ sint.Z j < sint.Z (W64 6) by word)]
      (try simp only [Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
      (try wp_auto)
      (try rw [decide_eq_false (show ¬ ((#false : val) = (#true : val)) by simp [intoVal_eq_iff])])
      (try simp only [Bool.false_eq_true, ↓reduceIte])
      (try wp_auto)
      (try simp only [decide_true, ↓reduceIte])
      (try wp_auto)
      (try simp only [decide_true, ↓reduceIte])
      (try wp_auto)
      iapply HΦ; iframe; ipureintro; intro _; exact hfit

end proof

end mvccfull
end EtcdGrove
end Perennial
