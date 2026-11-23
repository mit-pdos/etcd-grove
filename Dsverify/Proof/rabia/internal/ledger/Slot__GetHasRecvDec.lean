/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__GetHasRecvDec.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).GetHasRecvDec`.
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

theorem Slot.GetHasRecvDec.wp_proof : Slot.GetHasRecvDec.spec (GF := GF) := fun s γ q => by
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
      (True -∗ Φ #st.hasRecvDec)) $$ [AU Hγ]
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
  wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hlocked Hdone Hrecv Hdec Hps Hpsl Hpscap Hbs Hbsl
      Hbscap Hts Htsl Htscap Hγ Hwk]
  · inext
    unfold slotInv
    iexists st
    isplitl [Hwk]
    · iexact Hwk
    unfold slotFields
    iframe Hγ
    isplitl
    · iexists dec, ps, bs, ts, tl
      iframe Hdone Hrecv Hdec Hps Hpsl Hpscap Htl Hbs Hbsl Hbscap Hts Htsl Htscap
      iexact Hdecrep
    · ipureintro; exact Hwf
  iapply HΦ
  itrivial

end proof
end Perennial.rabia.internal.ledger
