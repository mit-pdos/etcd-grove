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
    have hW : ∀ k : Nat, k < 256 → (W8 ((k : Nat) : Int) : w8) = BitVec.ofNat 8 k := by
      intro k hk; apply BitVec.eq_of_toNat_eq; simp [W8]; omega
    cases st
    · simp only [nestRun] at hrun
      wp_auto
      wp_if_destruct
      · trace_state
        sorry
      · trace_state
        sorry
    · wp_auto
      wp_if_destruct
      · trace_state
        sorry
      · trace_state
        sorry
  · have hi : bs.length ≤ uint.nat i := by word
    rw [List.drop_eq_nil_of_le hi] at hrun
    simp only [nestRun] at hrun
    rw [hrun]
    iapply HΦ
    iframe

end proof

end models_lab.jsoncodec
end Perennial
