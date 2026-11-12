/- Lean-first (no Rocq counterpart). The proof of `hashing` (a loop over the first six weights, then
the sixth's test): Draft, to come (a leaf, not glue). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.hashing

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

/-- `hashing`'s loop's flag after `j` weights. -/
def anyPos (w : List Int) (j : Nat) : Bool := (List.range j).any fun i => decide (0 < w.getD i 0)

theorem anyPos_succ (w : List Int) (j : Nat) :
    anyPos w (j + 1) = (anyPos w j || decide (0 < w.getD j 0)) := by
  unfold anyPos; rw [List.range_succ, List.any_append]; simp

theorem anyPos_len (w : List Int) (j : Nat) (hj : w.length ≤ j) :
    anyPos w (j + 1) = anyPos w j := by
  have : w.getD j 0 = 0 := by simp [List.getD, List.getElem?_eq_none hj]
  rw [anyPos_succ, this]; simp

theorem anyPos_le (w : List Int) (j k : Nat) (hj : w.length ≤ j) (hk : j ≤ k) :
    anyPos w k = anyPos w j := by
  induction k with
  | zero => have : j = 0 := by omega
            subst this; rfl
  | succ k ih =>
    by_cases h : j = k + 1
    · subst h; rfl
    · rw [anyPos_len w k (by omega), ih (by omega)]

theorem hashing.wp_proof : hashing.spec (GF := GF) (hG := hG) := by
  intro w ws dq
  wp_start as Hw
  ihave %Hwl := ownSlice_len $$ Hw
  wp_auto
  have hget : ∀ (k : Nat) (v : w64), ws[k]? = some v → (ws.map sint.Z).getD k 0 = sint.Z v := by
    intro k v hv; simp [List.getD, List.getElem?_map, hv]
  ihave IH : (∃ (j : w64) (a : Bool),
      "i" ∷ i_ptr ↦ j ∗ "any" ∷ any_ptr ↦ a ∗ "w" ∷ w_ptr ↦ w ∗ "Hw" ∷ w ↦*{dq} ws ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 6 ∧ sint.Z j ≤ sint.Z w.len ∧
        a = anyPos (ws.map sint.Z) (sint.nat j)⌝ : IProp GF)
      $$ [i «any» w Hw]
  · iexists W64 0, false
    iframe
    ipureintro
    refine ⟨by word, by word, by word, rfl⟩
  wp_for IH
  obtain ⟨hj0, hj6, hjl, ha⟩ := Hj
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
    have hz := hget _ _ Hwj_lookup
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    by_cases hpos : sint.Z (W64 0) < sint.Z wj
    · rw [decide_eq_true hpos]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, true
      iframe
      ipureintro
      refine ⟨by word, by word, by word, ?_⟩
      rw [hj1, anyPos_succ, hz]; simp only [show (0 : Int) < sint.Z wj by simpa using hpos,
        decide_true, Bool.or_true]
    · rw [decide_eq_false hpos]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, a
      iframe
      ipureintro
      refine ⟨by word, by word, by word, ?_⟩
      rw [hj1, anyPos_succ, hz, ha]; simp only [show ¬ (0 : Int) < sint.Z wj by simpa using hpos,
        decide_false, Bool.or_false]
  · -- the loop's end: `any` is `anyPos` at 6
    have hend : a = anyPos (ws.map sint.Z) 6 := by
      rw [ha]
      by_cases h6 : sint.Z j < 6
      · have hjw : sint.Z w.len ≤ sint.Z j := by omega
        have hjn : sint.nat j = ws.length := by rw [Hwl.1]; word
        rw [hjn]; exact (anyPos_le _ _ 6 (by simp) (by rw [← hjn]; word)).symm
      · have : sint.nat j = 6 := by word
        rw [this]
    by_cases h6 : sint.Z j < 6
    · rw [decide_eq_true (show sint.Z j < sint.Z (W64 6) by word)]
      (try wp_auto)
      rw [decide_eq_false (show ¬ sint.Z j < sint.Z w.len by omega)]
      (try simp only [intoVal_eq_iff])
      (try simp only [Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
      (try simp only [intoVal_eq_iff])
      (try simp only [Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
      (try wp_auto)
      (try rw [decide_eq_false (show ¬ ((#false : val) = (#true : val)) by simp [intoVal_eq_iff])])
      (try simp only [Bool.false_eq_true, ↓reduceIte])
      (try wp_auto)
      have hm : hashingM (ws.map sint.Z) = Bool.or (!a) (decide (0 < (ws.map sint.Z).getD 5 0)) := by
        rw [hend]; rfl
      cases a
      · (try simp only [Bool.not_false, decide_True_any, decide_true, ↓reduceIte])
        (try wp_auto)
        iapply HΦ; iframe; ipureintro; rw [hm]; rfl
      · (try simp only [Bool.not_true, Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
        (try wp_auto)
        wp_if_destruct
        · have h5 : 5 < ws.length := by rw [Hwl.1]; word
          list_elem ws 5 as w5
          (try simp only [show 0 ≤ sint.Z (W64 5) ∧ sint.Z (W64 5) < sint.Z w.len by
            constructor <;> word, _root_.and_self, ↓reduceIte])
          wp_apply wp_load_slice_index w (sint.Z (W64 5)) ws dq w5 (by decide) $$ [Hw] as Hw
          · iframe; ipureintro; exact Hw5_lookup
          (try wp_auto)
          iapply HΦ; iframe; ipureintro
          rw [hm, hget 5 w5 Hw5_lookup]; simp
        · (try wp_auto)
          iapply HΦ; iframe; ipureintro
          have : (ws.map sint.Z).getD 5 0 = 0 := by
            simp [List.getD]; rw [List.getElem?_eq_none (by rw [Hwl.1]; word)]; rfl
          rw [hm, this]; rfl
    · rw [decide_eq_false (show ¬ sint.Z j < sint.Z (W64 6) by word)]
      (try simp only [intoVal_eq_iff])
      (try simp only [Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
      (try simp only [intoVal_eq_iff])
      (try simp only [Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
      (try wp_auto)
      (try rw [decide_eq_false (show ¬ ((#false : val) = (#true : val)) by simp [intoVal_eq_iff])])
      (try simp only [Bool.false_eq_true, ↓reduceIte])
      (try wp_auto)
      have hm : hashingM (ws.map sint.Z) = Bool.or (!a) (decide (0 < (ws.map sint.Z).getD 5 0)) := by
        rw [hend]; rfl
      cases a
      · (try simp only [Bool.not_false, decide_True_any, decide_true, ↓reduceIte])
        (try wp_auto)
        iapply HΦ; iframe; ipureintro; rw [hm]; rfl
      · (try simp only [Bool.not_true, Bool.false_eq_true, decide_False_any, decide_True_any, decide_eq_self_any, ↓reduceIte])
        (try wp_auto)
        wp_if_destruct
        · have h5 : 5 < ws.length := by rw [Hwl.1]; word
          list_elem ws 5 as w5
          (try simp only [show 0 ≤ sint.Z (W64 5) ∧ sint.Z (W64 5) < sint.Z w.len by
            constructor <;> word, _root_.and_self, ↓reduceIte])
          wp_apply wp_load_slice_index w (sint.Z (W64 5)) ws dq w5 (by decide) $$ [Hw] as Hw
          · iframe; ipureintro; exact Hw5_lookup
          (try wp_auto)
          iapply HΦ; iframe; ipureintro
          rw [hm, hget 5 w5 Hw5_lookup]; simp
        · (try wp_auto)
          iapply HΦ; iframe; ipureintro
          have : (ws.map sint.Z).getD 5 0 = 0 := by
            simp [List.getD]; rw [List.getElem?_eq_none (by rw [Hwl.1]; word)]; rfl
          rw [hm, this]; rfl

end proof

end mvccfull
end EtcdGrove
end Perennial
