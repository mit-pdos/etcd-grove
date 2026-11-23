/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__GetDecisionOrWake.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).GetDecisionOrWake` (R1-wake).

Under the slot's lock: reads the decision state (the atomic update commits there, the state
unchanged); if the slot is not done, takes the wake channel from the lock's invariant (`wakeRep`:
`nil`, or a pending broadcast channel), making it if `nil`, and returns its persistent `Unknown`
view; the pending ownership stays in the invariant, for `SetDecision` to close.
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

theorem Slot.GetDecisionOrWake.wp_proof : Slot.GetDecisionOrWake.spec (GF := GF) := fun s γ q => by
  iintro #Hpkg #Hslot
  ihave ⟨#Hsync, #Hsort, #Hmsg⟩ := ledgerDeps $$ Hpkg
  unfold isSlot
  icases Hslot with ⟨#Hq, #Ht, #Hm⟩
  unfold atomic_wp
  iintro %Φ AU
  wp_method_call
  wp_call
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hm] as ⟨Hlocked, Hinv⟩
  iNamed Hinv
  iNamed Hf
  ihave HΦ : |={⊤}=> (ghostVar γ (1 : Qp).half st ∗
      ∀ (v : ConsensusObj) (w : GoChan),
        (if st.isDone then objRep v st.decision
         else ∃ γw : ChanNames, ownBroadcastChan w γw iprop(True) .Unknown) -∗
        Φ (PairV (PairV #v #st.isDone) #w)) $$ [AU Hγ]
  · imod AU with ⟨%x, Hst, -, Hcommit⟩
    rcases x with ⟨st0, ⟨⟩⟩
    dsimp only [Tele.app]
    unfold slotSt
    icombine Hγ Hst gives %H
    obtain ⟨_, Heq⟩ := H
    subst Heq
    imod Hcommit $$ %() Hst with HΦ
    imodintro
    iframe Hγ
    dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
    iexact HΦ
  iapply fupd_wp
  imod HΦ with ⟨Hγ, HΦ⟩
  imodintro
  wp_auto
  cases hd : st.isDone
  · -- not done: the wake channel (made if `nil`); its pending ownership stays in the invariant
    unfold wakeRep
    icases Hwk with ⟨%w, Hw, Hor⟩
    wp_auto
    wp_if_destruct
    · -- `wake == nil`: a new broadcast channel
      wp_apply (chan.wp_make1 (V := Unit)) as %ch %γw ⟨#Hch, %Hcap, Hown⟩
      imod alloc_broadcast_chan iprop(True) γw ch $$ Hch Hown with Hb
      icases ownBroadcastChan_pending_unknown _ _ _ $$ Hb with ⟨Hb, #Hu⟩
      wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hlocked Hdone Hrecv Hdec Hps Hpsl Hpscap Hbs Hbsl
        Hbscap Hts Htsl Htscap Hγ Hw Hb]
      · inext
        unfold slotInv
        iexists st
        isplitl [Hw Hb]
        · rw [hd]
          unfold wakeRep
          iexists ch
          iframe Hw
          iright
          isplitr
          · ipureintro; rfl
          iexists γw
          iexact Hb
        unfold slotFields
        iframe Hγ
        isplitl
        · iexists dec, ps, bs, ts, tl
          rw [hd]
          iframe Hdone Hrecv Hdec Hps Hpsl Hpscap Htl Hbs Hbsl Hbscap Hts Htsl Htscap
          rw [← hd]
          iexact Hdecrep
        · ipureintro; exact Hwf
      iapply HΦ
      iexists γw
      iexact Hu
    · -- `wake != nil`: the pending broadcast channel of the invariant
      icases Hor with (%Hnil | ⟨-, %γw, Hb⟩)
      · exfalso; simp_all
      icases ownBroadcastChan_pending_unknown _ _ _ $$ Hb with ⟨Hb, #Hu⟩
      wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hlocked Hdone Hrecv Hdec Hps Hpsl Hpscap Hbs Hbsl
        Hbscap Hts Htsl Htscap Hγ Hw Hb]
      · inext
        unfold slotInv
        iexists st
        isplitl [Hw Hb]
        · rw [hd]
          unfold wakeRep
          iexists w
          iframe Hw
          iright
          isplitr
          · ipureintro; rfl
          iexists γw
          iexact Hb
        unfold slotFields
        iframe Hγ
        isplitl
        · iexists dec, ps, bs, ts, tl
          rw [hd]
          iframe Hdone Hrecv Hdec Hps Hpsl Hpscap Htl Hbs Hbsl Hbscap Hts Htsl Htscap
          rw [← hd]
          iexact Hdecrep
        · ipureintro; exact Hwf
      iapply HΦ
      iexists γw
      iexact Hu
  · -- done: the decision
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hlocked Hdone Hrecv Hdec Hps Hpsl Hpscap Hbs Hbsl
        Hbscap Hts Htsl Htscap Hγ Hwk]
    · inext
      unfold slotInv
      iexists st
      isplitl [Hwk]
      · rw [hd]; iexact Hwk
      unfold slotFields
      iframe Hγ
      isplitl
      · iexists dec, ps, bs, ts, tl
        rw [hd]
        iframe Hdone Hrecv Hdec Hps Hpsl Hpscap Htl Hbs Hbsl Hbscap Hts Htsl Htscap
        rw [← hd]
        iexact Hdecrep
      · ipureintro; exact Hwf
    iapply HΦ
    rw [ite_eq_left rfl]
    ihave Hx := decRep_elim _ _ _ $$ Hdecrep
    rw [ite_eq_left rfl]
    iexact Hx

end proof
end Perennial.rabia.internal.ledger
