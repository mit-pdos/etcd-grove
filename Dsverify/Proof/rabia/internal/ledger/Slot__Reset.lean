/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__Reset.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).Reset`.
-/
module

public import Dsverify.Proof.rabia.internal.ledger.Slot__wakeWaiters

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

/-- `Reset` at a configuration `choose` can pick (phase arrays of 2..10 entries). -/
theorem Slot.Reset.wp_proof_ok (cf : RCfg) (hc : cf.Ok) (s : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger ∗ rabia.internal.config.confRO cf ∗
        s ↦ (zeroValDef : Slot) }}
      (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"Reset")) (Val #()))
    {{ RET #(); |={⊤}=> ∃ γ q, isSlot s γ q ∗ slotSt γ (SlotSt.init cf.blockLen) ∗
        slotPriv s { phase := 0, round := 0, myProp := default, myBC := [] } ∗ queueFresh q }} := by
  obtain ⟨hL1, hL2⟩ := blockLen_ok hc
  have hn : sint.nat (W64 cf.blockLen) = cf.blockLen := by word
  wp_start as ⟨#Hconf, Hs⟩
  icases rabia.internal.config.confRO_val $$ Hconf with ⟨%cps, #Hc⟩
  ihave Hc2 := Hc
  iStructNamed Hc2
  iStructNamed Hs
  wp_auto
  -- R1-wake: a fresh slot's wake channel is `nil`: `wakeWaiters` closes nothing
  wp_apply Slot.wp_wakeWaiters s false $$ [wake] as Hwk
  · unfold wakeRep
    iexists _
    iframe wake
    ileft
    ipureintro; rfl
  wp_apply (chan.wp_make2 (V := Msg) (W64 10)) as %ch %γc ⟨#Hch, %Hcap, Hown⟩
  · ipureintro; decide
  wp_apply (wp_slice_make2 (V := Tally) (W64 0)) as %ps ⟨Hpsl, Hpscap⟩
  · ipureintro; decide
  wp_apply (wp_slice_make2 (V := GoArray w32 2) (W64 cf.blockLen)) as %msl ⟨Hmysl, Hmycap⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := GoArray (GoArray w64 3) 2) (W64 cf.blockLen)) as %bs ⟨Hbsl, Hbscap⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := GoArray w64 2) (W64 cf.blockLen)) as %ts ⟨Htsl, Htscap⟩
  · ipureintro; word
  iapply HΦ
  imod ghostVar_alloc (SlotSt.init cf.blockLen) with ⟨%γ, Hv⟩
  icases ghostVar_split γ (SlotSt.init cf.blockLen) (1 : Qp).half (1 : Qp).half $$ [Hv] with ⟨Hv1, Hv2⟩
  · rw [Qp.half_add_half]; iexact Hv
  have hinit : (SlotSt.init cf.blockLen).wf := by
    refine ⟨by simp [SlotSt.init], by simp [SlotSt.init], by simp [SlotSt.init], ?_, ?_, ?_, ?_, ?_⟩
    · intro p c t hc ht
      simp only [SlotSt.init, List.getElem?_replicate] at hc ht
      split at hc <;> split at ht <;> (try cases hc) <;> (try cases ht) <;> simp
    · intro t ht; simp [SlotSt.init] at ht; obtain ⟨-, rfl⟩ := ht; simp [cntOk]
    · simpa [SlotSt.init] using hL1
    · simp [SlotSt.init]
    · simp [SlotSt.init]; omega
  imod sync.init_Mutex (slotInv s γ) ⊤ (structFieldRef Slot go!"Lock" s) $$ Lock
    [IsDone HasRecvDec Decision RecvProposals Hpsl Hpscap RecvBCMsgs Hbsl Hbscap RecvBCMsgsT Htsl
      Htscap Hv2 Hwk] with #Hm
  · inext
    unfold slotInv
    iexists (SlotSt.init cf.blockLen)
    isplitl [Hwk]
    · unfold wakeRep
      iexists chan.nil
      iframe Hwk
      ileft
      ipureintro; rfl
    unfold slotFields
    iframe Hv2
    isplitl
    · iexists (Perennial.zero_val ConsensusObj), ps, bs, ts, []
      have e1 : (SlotSt.init cf.blockLen).bc.map encBC = List.replicate (sint.nat (W64 cf.blockLen)) (Perennial.zero_val (GoArray (GoArray w64 3) 2)) := by
        simp only [SlotSt.init, List.map_replicate, hn]; rfl
      have e2 : (SlotSt.init cf.blockLen).bcT.map encT = List.replicate (sint.nat (W64 cf.blockLen)) (Perennial.zero_val (GoArray w64 2)) := by
        simp only [SlotSt.init, List.map_replicate, hn]; rfl
      rw [e1, e2]
      simp only [List.replicate_zero] at *
      iframe
      simp only [SlotSt.init]
      isplitr
      · iapply decRep_false
      · iapply talliesRep_nil
    · ipureintro; exact hinit
  ipersist Queue
  ipersist Term
  imodintro
  iexists γ, ch
  isplitr
  · unfold isSlot
    iframe Queue Hm
    rw [show (W32 0) = (zeroValDef : Slot).Term' from rfl]
    iexact Term
  isplitl [Hv1]
  · unfold slotSt; iexact Hv1
  isplitr [Hown]
  · unfold slotPriv
    iexists (Perennial.zero_val ConsensusObj)
    dsimp only
    rw [show (0 : w32) = W32 0 from rfl]
    iframe Phase Round MyProposal
    isplitr
    · iapply objRep_zero
    unfold myRep
    iexists msl, _
    iframe MyBCMsgs Hmysl Hmycap
    ipureintro
    refine ⟨by simp, by simp; word, ?_⟩
    intro i h
    simp only [List.getElem_replicate, List.getD_nil]
    rfl
  · unfold queueFresh
    iexists γc
    iframe Hch Hown
    ipureintro; exact Hcap

theorem Slot.Reset.wp_proof : Slot.Reset.spec (GF := GF) := fun cf s => by
  by_cases hc : cf.Ok
  · exact Slot.Reset.wp_proof_ok (GF := GF) cf hc s
  · -- `confRO cf` carries `cf.Ok` (H2-ledger-1)
    iintro %Φ ⟨-, Hc, -⟩ -
    ihave %h := rabia.internal.config.confRO_ok cf $$ Hc
    exact absurd h hc

end proof
end Perennial.rabia.internal.ledger
