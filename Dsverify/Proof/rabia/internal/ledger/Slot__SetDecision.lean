/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__SetDecision.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).SetDecision`.
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

theorem Slot.SetDecision.wp_proof : Slot.SetDecision.spec (GF := GF) := fun s γ q v o => by
  iintro #Hpkg #Hslot #Hrep
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
  ihave HΦ : |={⊤}=> (ghostVar γ (1 : Qp).half { st with isDone := true, decision := o } ∗
      Φ #()) $$ [AU Hγ]
  · imod AU with ⟨%x, Hst, -, Hcommit⟩
    rcases x with ⟨st0, ⟨⟩⟩
    dsimp only [Tele.app]
    unfold slotSt
    icombine Hγ Hst gives %H
    obtain ⟨_, Heq⟩ := H
    subst Heq
    imod ghostVar_update_halves { st with isDone := true, decision := o } γ st st $$ Hγ Hst
      with ⟨Hγ, Hst⟩
    imod Hcommit $$ %() Hst with HΦ
    imodintro
    iframe Hγ
    dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
    iapply HΦ
    itrivial
  iapply fupd_wp
  imod HΦ with ⟨Hγ, HΦ⟩
  imodintro
  wp_auto
  wp_apply Slot.wp_wakeWaiters s st.isDone $$ [$Hwk] as Hwk
  wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hlocked Hdone Hrecv Hdec Hps Hpsl Hpscap Hbs Hbsl
      Hbscap Hts Htsl Htscap Hγ Hwk]
  · inext
    unfold slotInv
    iexists { st with isDone := true, decision := o }
    isplitl [Hwk]
    · unfold wakeRep
      iexists chan.nil
      iframe Hwk
      ileft
      ipureintro; rfl
    unfold slotFields
    iframe Hγ
    isplitl
    · iexists v, ps, bs, ts, tl
      iframe Hdone Hrecv Hdec Hps Hpsl Hpscap Htl Hbs Hbsl Hbscap Hts Htsl Htscap
      iapply decRep_of_objRep
      iexact Hrep
    · ipureintro; exact Hwf
  iexact HΦ

end proof
end Perennial.rabia.internal.ledger
