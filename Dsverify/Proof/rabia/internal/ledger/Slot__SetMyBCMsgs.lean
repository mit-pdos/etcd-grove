/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__SetMyBCMsgs.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).SetMyBCMsgs`.
-/
module

public import Dsverify.Proof.rabia.internal.ledger.Basics

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.ledger

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model rabia.internal.message

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.ledger.Assumptions]

theorem Slot.SetMyBCMsgs.wp_proof : Slot.SetMyBCMsgs.spec (GF := GF) :=
    fun s pv phase round x hr => by
  wp_start as H
  iNamed H
  iNamed Hmy
  obtain ⟨hml, hvl, hvs⟩ := Hmyrel
  wp_auto
  ihave HI : (∃ (msl' : GoSlice) (vs' : List (GoArray w32 2)),
      "Hmy" ∷ structFieldRef Slot go!"MyBCMsgs" s ↦ msl' ∗
      "Hmysl" ∷ msl' ↦* vs' ∗
      "Hmycap" ∷ ownSliceCap (GoArray w32 2) msl' (DFrac.own 1) ∗
      "%Hinv" ∷ ⌜(∀ i (h : i < vs'.length), vs'[i] = encMy (pv.myBC.getD i (0, 0))) ∧
        pv.myBC.length ≤ vs'.length ∧
        (vs'.length = vs.length ∨ vs'.length ≤ phase.toNat + 1 ∨ phase.toNat = 2 ^ 32 - 1)⌝ :
      IProp GF) $$ [Hmy Hmysl Hmycap]
  · iexists msl, vs
    iframe Hmy Hmysl Hmycap
    ipureintro
    exact ⟨hvs, hml, Or.inl rfl⟩
  wp_for HI
  ihave %Hl := ownSlice_len _ _ _ $$ Hmysl
  wp_if_destruct
  · wp_apply wp_slice_literal (V := GoArray w32 2) (t := go.ArrayType 2 go.uint32)
      [Perennial.zero_val (GoArray w32 2)]
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hz, Hzcap⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hmysl $Hmycap $Hz] as %ns ⟨Hmysl, Hmycap, -⟩
    wp_for_post
    iframe
    iexists ns, vs' ++ [Perennial.zero_val (GoArray w32 2)]
    iframe Hmy Hmysl Hmycap
    ipureintro
    have hz : Perennial.zero_val (GoArray w32 2) = encMy (0, 0) := rfl
    have hm : vs'.length % 2 ^ 32 ≤ phase.toNat := by
      have h1 := Hl.1; have h2 := Hl.2; word
    have hp := phase.isLt
    obtain ⟨h1, h2, h3⟩ := Hinv
    refine ⟨?_, by simp; omega, ?_⟩
    · intro i h
      rw [List.getElem_append]
      split
      · exact h1 i _
      · simp only [List.getElem_singleton]
        rw [hz]
        simp only [List.length_append, List.length_singleton] at h
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    · simp only [List.length_append, List.length_singleton]
      omega
  · have hp := phase.isLt
    obtain ⟨h1, h2, h3⟩ := Hinv
    have hlen : phase.toNat < vs'.length ∧ vs'.length < 2 ^ 32 := by
      have hm : ¬ vs'.length % 2 ^ 32 ≤ phase.toNat := by
        have h1 := Hl.1; have h2 := Hl.2; word
      omega
    have hpz : sint.Z (W64 (uint.Z phase)) = (phase.toNat : Int) := by word
    have hrz : sint.Z (W64 (uint.Z (round - W32 1))) = (round.toNat - 1 : Nat) := by
      rcases hr with rfl | rfl <;> rfl
    simp only [hpz, Int.natCast_nonneg, true_and, show (phase.toNat : Int) < sint.Z msl'.len by word,
      ↓reduceIte]
    wp_auto
    simp only [hrz, Int.natCast_nonneg, true_and, show ((round.toNat - 1 : Nat) : Int) < 2 by
      rcases hr with rfl | rfl <;> decide, ↓reduceIte]
    have ha : vs'[(phase.toNat : Int).toNat]? = some (encMy (pv.myBC.getD phase.toNat (0, 0))) := by
      rw [Int.toNat_natCast, List.getElem?_eq_getElem hlen.1, h1]
    obtain ⟨y, hy⟩ : ∃ y, (encMy (pv.myBC.getD phase.toNat (0, 0))).arr[((round.toNat - 1 : Nat) : Int).toNat]? = some y := by
      rw [Int.toNat_natCast]; unfold encMy
      exact ⟨_, List.getElem?_eq_getElem (by simp; rcases hr with rfl | rfl <;> decide)⟩
    icases slice_array_acc msl' _ vs' _ _ _ y (Int.natCast_nonneg _) (Int.natCast_nonneg _) ha hy
      $$ Hmysl with ⟨Hv, Hmysl⟩
    wp_auto
    ihave Hmysl := Hmysl $$ Hv
    iapply HΦ
    unfold slotPriv
    iexists mp
    simp only [PrivSt.setMy]
    iframe Hph Hrd Hmp Hmprep
    unfold myRep
    iexists msl', _
    iframe Hmy Hmycap
    rw [Int.toNat_natCast, Int.toNat_natCast]
    iframe Hmysl
    ipureintro
    exact myRel_setMy pv vs' phase.toNat round.toNat x
      (by rcases hr with rfl | rfl <;> simp) h1 h2 hlen.1 hlen.2

end proof
end Perennial.rabia.internal.ledger
