/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__recvBCMsgsT.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).recvBCMsgsT`.
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

/-- `s.recvBCMsgsT(phase, round)` (called holding the lock): the total of `phase`, `round`. -/
theorem Slot.wp_recvBCMsgsT (s : Loc) (ts : GoSlice) (st : SlotSt) (phase round : w32)
    (hr : round = 1 ∨ round = 2) (hl : st.bcT.length < 2 ^ 32) :
    {{ (structFieldRef Slot go!"RecvBCMsgsT" s ↦ ts ∗ ts ↦* st.bcT.map encT : IProp GF) }}
      (App (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"recvBCMsgsT")) (Val #phase))
        (Val #round))
    {{ RET #(W64 (st.total phase.toNat round.toNat : Nat));
        structFieldRef Slot go!"RecvBCMsgsT" s ↦ ts ∗ ts ↦* st.bcT.map encT }} := by
  wp_start as ⟨Hts, Htsl⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Htsl
  wp_auto
  rw [List.length_map] at Hl
  have hlen : uint.Z (W32 (sint.Z ts.len)) = (st.bcT.length : Int) := by word
  wp_if_destruct
  · have hnone : st.bcT[phase.toNat]? = none := List.getElem?_eq_none (by word)
    have hc : st.total phase.toNat round.toNat = 0 := by
      unfold SlotSt.total; rw [hnone]
    rw [hc]
    iapply HΦ
    iframe Hts Htsl
  · have hpl : phase.toNat < st.bcT.length := by word
    list_elem st.bcT phase.toNat as c
    have hpz : sint.Z (W64 (uint.Z phase)) = (phase.toNat : Int) := by word
    have hrz : sint.Z (W64 (uint.Z (round - W32 1))) = (round.toNat - 1 : Nat) := by
      rcases hr with rfl | rfl <;> rfl
    have ha : (st.bcT.map encT)[(phase.toNat : Int).toNat]? = some (encT c) := by
      rw [Int.toNat_natCast, List.getElem?_map, Hc_lookup]; rfl
    have hv : (encT c).arr[((round.toNat - 1 : Nat) : Int).toNat]? =
        some (W64 ((if round.toNat = 1 then c.1 else c.2 : Nat) : Int)) := by
      rw [Int.toNat_natCast]; unfold encT
      rcases hr with rfl | rfl <;> rfl
    icases slice_array_acc ts _ (st.bcT.map encT) _ _ _ _ (Int.natCast_nonneg _)
      (Int.natCast_nonneg _) ha hv $$ Htsl with ⟨Hv, Htsl⟩
    simp only [hpz, Int.natCast_nonneg, _root_.true_and,
      show (phase.toNat : Int) < sint.Z ts.len by word, ↓reduceIte]
    wp_auto
    simp only [hrz, Int.natCast_nonneg, _root_.true_and, show ((round.toNat - 1 : Nat) : Int) < 2 by
      rcases hr with rfl | rfl <;> decide, ↓reduceIte]
    wp_auto
    ihave Htsl := Htsl $$ Hv
    rw [Int.toNat_natCast, Int.toNat_natCast]
    rw [show array.mk 2 ((encT c).arr.set (round.toNat - 1)
        (W64 ((if round.toNat = 1 then c.1 else c.2 : Nat) : Int))) = encT c by
      unfold encT; rcases hr with rfl | rfl <;> rfl]
    have ha' : (st.bcT.map encT)[phase.toNat]? = some (encT c) := by
      rw [List.getElem?_map, Hc_lookup]; rfl
    rw [list_set_lookup_self _ _ _ ha']
    have hc : st.total phase.toNat round.toNat = if round.toNat = 1 then c.1 else c.2 := by
      unfold SlotSt.total; rw [Hc_lookup]
    rw [hc]
    iapply HΦ
    iframe Hts Htsl

end proof
end Perennial.rabia.internal.ledger
