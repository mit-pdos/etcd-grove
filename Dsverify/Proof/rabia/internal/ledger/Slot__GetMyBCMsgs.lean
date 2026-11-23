/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__GetMyBCMsgs.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).GetMyBCMsgs`.
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

theorem Slot.GetMyBCMsgs.wp_proof : Slot.GetMyBCMsgs.spec (GF := GF) :=
    fun s pv phase round hr hp => by
  wp_start as H
  iNamed H
  iNamed Hmy
  ihave %Hl := ownSlice_len _ _ _ $$ Hmysl
  obtain ⟨hml, hvl, hvs⟩ := Hmyrel
  have hpz : sint.Z (W64 (uint.Z phase)) = (phase.toNat : Int) := by word
  have hpl : phase.toNat < vs.length := by omega
  have hrz : sint.Z (W64 (uint.Z (round - W32 1))) = (round.toNat - 1 : Nat) := by
    rcases hr with rfl | rfl <;> rfl
  have hr2 : round.toNat - 1 < 2 := by rcases hr with rfl | rfl <;> decide
  wp_auto
  simp only [hpz, Int.natCast_nonneg, true_and, show (phase.toNat : Int) < sint.Z msl.len by word,
    ↓reduceIte]
  wp_auto
  simp only [hrz, Int.natCast_nonneg, true_and, show ((round.toNat - 1 : Nat) : Int) < 2 by omega,
    ↓reduceIte]
  have ha : vs[(phase.toNat : Int).toNat]? = some (encMy (pv.myBC.getD phase.toNat (0, 0))) := by
    rw [Int.toNat_natCast, List.getElem?_eq_getElem hpl, hvs]
  obtain ⟨x, hx⟩ : ∃ x, (encMy (pv.myBC.getD phase.toNat (0, 0))).arr[((round.toNat - 1 : Nat) : Int).toNat]? = some x := by
    rw [Int.toNat_natCast]; unfold encMy
    exact ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
  icases slice_array_acc msl _ vs _ _ _ x (Int.natCast_nonneg _) (Int.natCast_nonneg _) ha hx $$ Hmysl
    with ⟨Hv, Hmysl⟩
  wp_auto
  ihave Hmysl := Hmysl $$ Hv
  rw [list_set_lookup_self _ _ _ hx]
  rw [show array.mk 2 (encMy (pv.myBC.getD phase.toNat (0, 0))).arr =
    encMy (pv.myBC.getD phase.toNat (0, 0)) from rfl, list_set_lookup_self _ _ _ ha]
  have hxv : x = pv.my phase.toNat round.toNat := by
    unfold PrivSt.my
    rw [Int.toNat_natCast] at hx
    obtain ⟨⟨a, b⟩, hab⟩ : ∃ p, pv.myBC[phase.toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem hp⟩
    rw [hab]
    rw [List.getD_eq_getElem?_getD, hab, Option.getD_some] at hx
    unfold encMy at hx
    rcases hr with rfl | rfl
    · simp at hx; simp [hx]
    · simp at hx; simp [hx]
  rw [hxv]
  iapply HΦ
  unfold slotPriv
  iexists mp
  iframe Hph Hrd Hmp Hmprep
  unfold myRep
  iexists msl, vs
  iframe Hmy Hmysl Hmycap
  ipureintro
  exact ⟨hml, hvl, hvs⟩

end proof
end Perennial.rabia.internal.ledger
