/-
The proof of `jsoncodec.Nesting` (`Net/Spec/models_lab/jsoncodec/Nesting.lean`): the loop against
`nestRun` (`Compact.lean`). New in dsv-vr round 9.
-/
module

public import Net.Spec.models_lab.jsoncodec.Nesting
public import Net.Proof.models_lab.jsoncodec.ScanString

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

theorem nestRun_esc (d m : w64) (l : List w8) :
    nestRun d m true (92#8 :: l) = nestRun d m true l.tail := by
  cases l with
  | nil => simp [nestRun]
  | cons y r => simp [nestRun]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- A loop turn's end: `i + 1`, the state `hrun` names. -/
local macro "nclose" h:term : tactic => `(tactic| (
  try wp_auto
  wp_for_post
  iframe
  iexists _, _, _, _
  iframe
  ipureintro
  rw [hi1]
  exact ⟨by omega, $h⟩))

theorem Nesting.wp_proof : Nesting.spec (GF := GF) (hG := hG) := by
  intro b dq bs hl
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  wp_auto
  ihave IH : iprop(∃ (i d m : w64) (st : Bool),
      "i" ∷ i_ptr ↦ i ∗ "depth" ∷ depth_ptr ↦ d ∗ "max" ∷ max_ptr ↦ m ∗ "inStr" ∷ inStr_ptr ↦ st ∗
      "%Hi" ∷ ⌜uint.nat i ≤ bs.length ∧
        nestRun d m st (bs.drop (uint.nat i)) = nestRun (W64 0) (W64 0) false bs⌝)
    $$ [i depth max inStr]
  · iexists _, _, _, _
    iframe
    ipureintro
    exact ⟨by word, by simp⟩
  wp_for IH
  obtain ⟨hil, hrun⟩ := Hi
  ihave %Hwf := ownSlice_wf $$ Hs
  wp_if_destruct
  · have Hlt : uint.nat i < bs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, bs[uint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hdrop : bs.drop (uint.nat i) = x :: bs.drop (uint.nat i + 1) := by
      rw [List.drop_eq_getElem_cons Hlt]; simp only [List.getElem?_eq_getElem Hlt] at Hx; cases Hx; rfl
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.len := by word
    have hnz : (sint.Z i).toNat = uint.nat i := by word
    rw [if_pos hb]
    wp_apply wp_load_slice_index b (sint.Z i) bs dq x hb.1 $$ [Hs] as Hs
    · iframe; ipureintro; rw [hnz]; exact Hx
    rw [hdrop] at hrun
    have hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
    have e34 : (W8 34 : w8) = 34#8 := by decide
    have e91 : (W8 91 : w8) = 91#8 := by decide
    have e123 : (W8 123 : w8) = 123#8 := by decide
    have e93 : (W8 93 : w8) = 93#8 := by decide
    have e125 : (W8 125 : w8) = 125#8 := by decide
    have e92 : (W8 92 : w8) = 92#8 := by decide
    cases st
    · simp only [nestRun] at hrun
      wp_auto
      by_cases h34 : x = W8 34
      · subst h34
        simp (config := { decide := true }) only [e34, ↓reduceIte] at hrun
        rw [decide_eq_true rfl]
        nclose hrun
      rw [decide_eq_false h34]
      rw [e34] at h34
      simp only [h34, ↓reduceIte] at hrun
      wp_auto
      by_cases h91 : x = W8 91 ∨ x = W8 123
      · have hrun' : nestRun (d + W64 1) (if uint.Z (d + W64 1) > uint.Z m then d + W64 1 else m)
            false (bs.drop (uint.nat i + 1)) = nestRun (W64 0) (W64 0) false bs := by
          rcases h91 with e | e <;> subst e <;>
            simpa (config := { decide := true }) only [e91, e123, ↓reduceIte] using hrun
        rcases h91 with e | e <;> subst e
        · rw [decide_eq_true rfl]
          wp_auto
          wp_if_destruct
          · rw [if_pos Hif] at hrun'; nclose hrun'
          · rw [if_neg Hif] at hrun'; nclose hrun'
        · rw [decide_eq_false (by decide)]
          wp_auto
          try rw [decide_eq_true rfl]
          try wp_auto
          wp_if_destruct
          · rw [if_pos Hif] at hrun'; nclose hrun'
          · rw [if_neg Hif] at hrun'; nclose hrun'
      have h91' : ¬ (x = 91#8 ∨ x = 123#8) := by rw [← e91, ← e123]; exact h91
      simp only [h91', ↓reduceIte] at hrun
      rw [not_or] at h91
      rw [decide_eq_false h91.1]
      wp_auto
      rw [decide_eq_false h91.2]
      wp_auto
      by_cases h93 : x = W8 93 ∨ x = W8 125
      · have hrun' : nestRun (d - W64 1) m false (bs.drop (uint.nat i + 1)) =
            nestRun (W64 0) (W64 0) false bs := by
          rcases h93 with e | e <;> subst e <;>
            simpa (config := { decide := true }) only [e93, e125, ↓reduceIte] using hrun
        rcases h93 with e | e <;> subst e
        · rw [decide_eq_true rfl]
          nclose hrun'
        · rw [decide_eq_false (by decide)]
          wp_auto
          try rw [decide_eq_true rfl]
          nclose hrun'
      have h93' : ¬ (x = 93#8 ∨ x = 125#8) := by rw [← e93, ← e125]; exact h93
      simp only [h93', ↓reduceIte] at hrun
      rw [not_or] at h93
      rw [decide_eq_false h93.1]
      wp_auto
      rw [decide_eq_false h93.2]
      nclose hrun
    · wp_auto
      by_cases h92 : x = W8 92
      · subst h92
        rw [e92, nestRun_esc] at hrun
        rw [decide_eq_true rfl]
        have hi2 : uint.nat i + 1 < bs.length := by
          rcases Nat.lt_or_ge (uint.nat i + 1) bs.length with h | h
          · exact h
          · exfalso; apply hl
            have hlen1 : uint.nat i + 1 = bs.length := by omega
            rw [List.getLast?_eq_getElem?]
            rw [show bs.length - 1 = uint.nat i by omega, Hx, e92]
        wp_auto
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
        ipureintro
        have hi2' : uint.nat (i + W64 1 + W64 1) = uint.nat i + 2 := by word
        rw [hi2']
        refine ⟨by omega, ?_⟩
        rw [show uint.nat i + 2 = (uint.nat i + 1) + 1 by omega, ← List.drop_drop, List.drop_one]
        exact hrun
      rw [decide_eq_false h92]
      rw [e92] at h92
      rw [nestRun.eq_def] at hrun
      simp only [h92, ↓reduceIte] at hrun
      wp_auto
      by_cases h34 : x = W8 34
      · subst h34
        simp (config := { decide := true }) only [e34, ↓reduceIte] at hrun
        rw [decide_eq_true rfl]
        nclose hrun
      rw [decide_eq_false h34]
      rw [e34] at h34
      simp only [h34, ↓reduceIte] at hrun
      nclose hrun
  · have hi : bs.length ≤ uint.nat i := by word
    rw [List.drop_eq_nil_of_le hi] at hrun
    simp only [nestRun] at hrun
    rw [hrun]
    iapply HΦ
    iframe

end proof

end models_lab.jsoncodec
end Perennial
