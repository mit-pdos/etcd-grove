/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__PutRecvBCMsgs.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).PutRecvBCMsgs`.
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

theorem Slot.PutRecvBCMsgs.wp_proof : Slot.PutRecvBCMsgs.spec (GF := GF) :=
    fun s γ q phase round x hr hx => by
  iintro #Hpkg #Hslot
  ihave ⟨#Hsync, #Hsort, #Hmsg⟩ := ledgerDeps $$ Hpkg
  unfold isSlot
  icases Hslot with ⟨#Hq, #Ht, #Hm⟩
  unfold atomic_wp
  iintro %Φ AU
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hm] as ⟨Hlocked, Hinv⟩
  iNamed Hinv
  ihave HΦ : |={⊤}=> (⌜cntOk (st.total phase.toNat round.toNat + 1)⌝ ∗ ghostVar γ (1 : Qp).half (st.put phase.toNat round.toNat x.toNat) ∗
      (True -∗ Φ #())) $$ [AU Hγ]
  · imod AU with ⟨%x, Hα, -, Hcommit⟩
    rcases x with ⟨st0, ⟨⟩⟩
    dsimp only [Tele.app]
    icases Hα with ⟨Hst, %Hbnd⟩
    unfold slotSt
    icombine Hγ Hst gives %H
    obtain ⟨_, Heq⟩ := H
    subst Heq
    imod ghostVar_update_halves (st.put phase.toNat round.toNat x.toNat) γ st st $$ Hγ Hst
      with ⟨Hγ, Hst⟩
    imod Hcommit $$ %() Hst with HΦ
    imodintro
    iframe Hγ
    isplitr
    · ipureintro; exact Hbnd
    dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
    iexact HΦ
  iapply fupd_wp
  imod HΦ with ⟨%hb, Hγ, HΦ⟩
  imodintro
  iNamed Hf
  obtain ⟨-, -, -, -, -, hw6, hw7, hw8⟩ := id Hwf
  ihave HI : (∃ (bs' ts' : GoSlice) (k : Nat),
      "Hbs" ∷ structFieldRef Slot go!"RecvBCMsgs" s ↦ bs' ∗
      "Hbsl" ∷ bs' ↦* (st.bc ++ List.replicate k ((0, 0, 0), (0, 0, 0))).map encBC ∗
      "Hbscap" ∷ ownSliceCap (GoArray (GoArray w64 3) 2) bs' (DFrac.own 1) ∗
      "Hts" ∷ structFieldRef Slot go!"RecvBCMsgsT" s ↦ ts' ∗
      "Htsl" ∷ ts' ↦* (st.bcT ++ List.replicate k (0, 0)).map encT ∗
      "Htscap" ∷ ownSliceCap (GoArray w64 2) ts' (DFrac.own 1) ∗
      "%Hk" ∷ ⌜k = 0 ∨ st.bc.length + k ≤ phase.toNat + 1 ∨ phase.toNat = 2 ^ 32 - 1⌝ :
      IProp GF) $$ [Hbs Hbsl Hbscap Hts Htsl Htscap]
  · iexists bs, ts, 0
    simp only [List.replicate_zero, List.append_nil]
    iframe Hbs Hbsl Hbscap Hts Htsl Htscap
    ipureintro; simp
  wp_for HI
  ihave %Hl := ownSlice_len _ _ _ $$ Hbsl
  rw [List.length_map, List.length_append, List.length_replicate] at Hl
  wp_if_destruct
  · wp_apply wp_slice_literal (V := GoArray (GoArray w64 3) 2)
      (t := go.ArrayType 2 (go.ArrayType 3 go.int)) [Perennial.zero_val (GoArray (GoArray w64 3) 2)]
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hz, Hzcap⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hbsl $Hbscap $Hz] as %nb ⟨Hbsl, Hbscap, -⟩
    wp_apply wp_slice_literal (V := GoArray w64 2)
      (t := go.ArrayType 2 go.int) [Perennial.zero_val (GoArray w64 2)]
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr2 ⟨Hz2, Hzcap2⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Htsl $Htscap $Hz2] as %nt ⟨Htsl, Htscap, -⟩
    wp_for_post
    iframe
    iexists nb, nt, k + 1
    have hz1 : Perennial.zero_val (GoArray (GoArray w64 3) 2) = encBC ((0, 0, 0), (0, 0, 0)) := rfl
    have hz2 : Perennial.zero_val (GoArray w64 2) = encT (0, 0) := rfl
    rw [hz1, hz2, ← List.map_singleton (f := encBC), ← List.map_singleton (f := encT),
      ← List.map_append, ← List.map_append, List.append_assoc, List.append_assoc,
      ← List.replicate_succ', ← List.replicate_succ']
    iframe Hbs Hbsl Hbscap Hts Htsl Htscap
    ipureintro
    have hm : (st.bc.length + k) % 2 ^ 32 ≤ phase.toNat := by
      have h1 := Hl.1; have h2 := Hl.2; word
    have hp := phase.isLt
    omega
  · have hp := phase.isLt
    have hm : ¬ (st.bc.length + k) % 2 ^ 32 ≤ phase.toNat := by
      have h1 := Hl.1; have h2 := Hl.2; word
    have hk' : k = phase.toNat + 1 - st.bc.length := by omega
    have hp1 : phase.toNat + 1 < 2 ^ 32 := by omega
    subst hk'
    rw [hw7]
    have hpB : phase.toNat < (st.bc ++ List.replicate (phase.toNat + 1 - st.bcT.length)
        ((0, 0, 0), (0, 0, 0))).length := by simp; omega
    have hpT : phase.toNat < (st.bcT ++ List.replicate (phase.toNat + 1 - st.bcT.length)
        (0, 0)).length := by simp; omega
    list_elem (st.bc ++ List.replicate (phase.toNat + 1 - st.bcT.length) ((0, 0, 0), (0, 0, 0)))
      phase.toNat as c
    list_elem (st.bcT ++ List.replicate (phase.toNat + 1 - st.bcT.length) (0, 0)) phase.toNat as t
    have hpz : sint.Z (W64 (uint.Z phase)) = (phase.toNat : Int) := by word
    have hrz : sint.Z (W64 (uint.Z (round - W32 1))) = (round.toNat - 1 : Nat) := by
      rcases hr with rfl | rfl <;> rfl
    have hxz : sint.Z (W64 (uint.Z x)) = (x.toNat : Int) := by word
    have hbl : (phase.toNat : Int) < sint.Z bs'.len := by
      have h1 := Hl.1; simp only [hw7] at h1; word
    ihave %Htl0 := ownSlice_len _ _ _ $$ Htsl
    have htl : (phase.toNat : Int) < sint.Z ts'.len := by
      rw [List.length_map] at Htl0; have h1 := Htl0.1; have h2 := Htl0.2; word
    have hr2 : ((round.toNat - 1 : Nat) : Int) < 2 := by rcases hr with rfl | rfl <;> decide
    have hx3 : (x.toNat : Int) < 3 := by omega
    generalize hB : st.bc ++ List.replicate (phase.toNat + 1 - st.bcT.length) ((0, 0, 0), (0, 0, 0))
      = B at Hc_lookup hpB
    generalize hT : st.bcT ++ List.replicate (phase.toNat + 1 - st.bcT.length) (0, 0)
      = T at Ht_lookup hpT
    have ha : (B.map encBC)[((phase.toNat : Nat) : Int).toNat]? = some (encBC c) := by
      rw [Int.toNat_natCast, List.getElem?_map, Hc_lookup]; rfl
    have hb' : (encBC c).arr[((round.toNat - 1 : Nat) : Int).toNat]? =
        some (encC (if round.toNat = 1 then c.1 else c.2)) := by
      rw [Int.toNat_natCast]; unfold encBC; rcases hr with rfl | rfl <;> rfl
    have hv : (encC (if round.toNat = 1 then c.1 else c.2)).arr[((x.toNat : Nat) : Int).toNat]? =
        some (W64 ((Counts.get x.toNat (if round.toNat = 1 then c.1 else c.2) : Nat) : Int)) := by
      rw [Int.toNat_natCast]; unfold encC Counts.get
      have hx' : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 := by omega
      rcases hx' with h | h | h <;> simp [h]
    icases slice_array2_acc bs' _ (B.map encBC) _ _ _ _ _ _ (Int.natCast_nonneg _)
      (Int.natCast_nonneg _) (Int.natCast_nonneg _) ha hb' hv $$ Hbsl with ⟨Hv, Hbsl⟩
    have hta : (T.map encT)[((phase.toNat : Nat) : Int).toNat]? = some (encT t) := by
      rw [Int.toNat_natCast, List.getElem?_map, Ht_lookup]; rfl
    have htv : (encT t).arr[((round.toNat - 1 : Nat) : Int).toNat]? =
        some (W64 ((if round.toNat = 1 then t.1 else t.2 : Nat) : Int)) := by
      rw [Int.toNat_natCast]; unfold encT; rcases hr with rfl | rfl <;> rfl
    icases slice_array_acc ts' _ (T.map encT) _ _ _ _ (Int.natCast_nonneg _)
      (Int.natCast_nonneg _) hta htv $$ Htsl with ⟨Htv, Htsl⟩
    repeat (simp only [hpz, hrz, hxz, hbl, htl, hr2, hx3, Int.natCast_nonneg,
      _root_.and_self, ↓reduceIte]; wp_auto)
    ihave Hbsl := Hbsl $$ Hv
    ihave Htsl := Htsl $$ Htv
    have hr' : round.toNat = 1 ∨ round.toNat = 2 := by rcases hr with rfl | rfl <;> decide
    simp only [Int.toNat_natCast]
    rw [encBC_incr B _ _ _ c hr' hx Hc_lookup, encT_incr T _ _ t hr' Ht_lookup]
    have e1 : (st.put phase.toNat round.toNat x.toNat).bc =
        B.modify phase.toNat (incBC round.toNat x.toNat) := by
      rw [st.put_bc, ← hB, hw7]
    have e2 : (st.put phase.toNat round.toNat x.toNat).bcT = T.modify phase.toNat (incT round.toNat) := by
      rw [st.put_bcT, ← hT]
    rw [← e1, ← e2]
    have hwf' := st.wf_put phase.toNat round.toNat x.toNat Hwf hb hp1
    wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hlocked Hdone Hrecv Hdec Hps Hpsl Hpscap Hbs Hbsl
        Hbscap Hts Htsl Htscap Hγ Hwk]
    · inext
      unfold slotInv
      iexists st.put phase.toNat round.toNat x.toNat
      isplitl [Hwk]
      · simp only [SlotSt.put]; iexact Hwk
      unfold slotFields
      iframe Hγ
      isplitl
      · iexists dec, ps, bs', ts', tl
        simp only [SlotSt.put_isDone, SlotSt.put_hasRecvDec, SlotSt.put_decision,
          SlotSt.put_props]
        iframe Hdone Hrecv Hdec Hps Hpsl Hpscap Htl Hbs Hbsl Hbscap Hts Htsl Htscap Hdecrep
      · ipureintro; exact hwf'
    iapply HΦ
    itrivial

end proof
end Perennial.rabia.internal.ledger
