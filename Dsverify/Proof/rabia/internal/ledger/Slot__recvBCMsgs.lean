/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__recvBCMsgs.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).recvBCMsgs`.
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

/-- `s.recvBCMsgs(phase, round)` (called holding the lock): the counts of `phase`, `round`. -/
theorem Slot.wp_recvBCMsgs (s : Loc) (bs : GoSlice) (st : SlotSt) (phase round : w32)
    (hr : round = 1 ∨ round = 2) (hl : st.bc.length < 2 ^ 32) :
    {{ (structFieldRef Slot go!"RecvBCMsgs" s ↦ bs ∗ bs ↦* st.bc.map encBC : IProp GF) }}
      (App (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"recvBCMsgs")) (Val #phase))
        (Val #round))
    {{ RET #(encC (st.counts phase.toNat round.toNat));
        structFieldRef Slot go!"RecvBCMsgs" s ↦ bs ∗ bs ↦* st.bc.map encBC }} := by
  wp_start as ⟨Hbs, Hbsl⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hbsl
  wp_auto
  rw [List.length_map] at Hl
  have hlen : uint.Z (W32 (sint.Z bs.len)) = (st.bc.length : Int) := by word
  wp_if_destruct
  · have hnone : st.bc[phase.toNat]? = none := List.getElem?_eq_none (by word)
    have hc : st.counts phase.toNat round.toNat = (0, 0, 0) := by
      unfold SlotSt.counts; rw [hnone]
    rw [hc, show encC (0, 0, 0) = Perennial.zero_val (GoArray w64 3) from rfl]
    iapply HΦ
    iframe Hbs Hbsl
  · have hpl : phase.toNat < st.bc.length := by word
    list_elem st.bc phase.toNat as c
    have hpz : sint.Z (W64 (uint.Z phase)) = (phase.toNat : Int) := by word
    have hrz : sint.Z (W64 (uint.Z (round - W32 1))) = (round.toNat - 1 : Nat) := by
      rcases hr with rfl | rfl <;> rfl
    have ha : (st.bc.map encBC)[(phase.toNat : Int).toNat]? = some (encBC c) := by
      rw [Int.toNat_natCast, List.getElem?_map, Hc_lookup]; rfl
    have hv : (encBC c).arr[((round.toNat - 1 : Nat) : Int).toNat]? =
        some (encC (if round.toNat = 1 then c.1 else c.2)) := by
      rw [Int.toNat_natCast]; unfold encBC
      rcases hr with rfl | rfl <;> rfl
    icases slice_array_acc bs _ (st.bc.map encBC) _ _ _ _ (Int.natCast_nonneg _)
      (Int.natCast_nonneg _) ha hv $$ Hbsl with ⟨Hv, Hbsl⟩
    simp only [hpz, Int.natCast_nonneg, _root_.true_and, show (phase.toNat : Int) < sint.Z bs.len by word,
      ↓reduceIte]
    wp_auto
    simp only [hrz, Int.natCast_nonneg, _root_.true_and, show ((round.toNat - 1 : Nat) : Int) < 2 by
      rcases hr with rfl | rfl <;> decide, ↓reduceIte]
    wp_auto
    ihave Hbsl := Hbsl $$ Hv
    rw [Int.toNat_natCast, Int.toNat_natCast]
    rw [show array.mk 2 ((encBC c).arr.set (round.toNat - 1) (encC (if round.toNat = 1 then c.1 else c.2))) = encBC c by
      unfold encBC; rcases hr with rfl | rfl <;> rfl]
    have ha' : (st.bc.map encBC)[phase.toNat]? = some (encBC c) := by
      rw [List.getElem?_map, Hc_lookup]; rfl
    rw [list_set_lookup_self _ _ _ ha']
    have hc : st.counts phase.toNat round.toNat = if round.toNat = 1 then c.1 else c.2 := by
      unfold SlotSt.counts; rw [Hc_lookup]
    rw [hc]
    iapply HΦ
    iframe Hbs Hbsl

end proof
end Perennial.rabia.internal.ledger
