/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__RecvBCMsgsMajV.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).RecvBCMsgsMajV`.
-/
module

public import Dsverify.Proof.rabia.internal.ledger.Slot__recvBCMsgs

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

theorem Slot.RecvBCMsgsMajV.wp_proof : Slot.RecvBCMsgsMajV.spec (GF := GF) :=
    fun s γ q phase round hr => by
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
  ihave HΦ : |={⊤}=> (ghostVar γ (1 : Qp).half st ∗
      (True -∗ Φ #(W32 ((st.counts phase.toNat round.toNat).majV : Nat)))) $$ [AU Hγ]
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
  iNamed Hf
  have hl : st.bc.length < 2 ^ 32 := Hwf.2.2.2.2.2.2.2
  wp_apply Slot.wp_recvBCMsgs s bs st phase round hr hl $$ [$Hbs $Hbsl] as ⟨Hbs, Hbsl⟩
  obtain ⟨hc1, hc2, -⟩ := st.wf_counts_ok Hwf phase.toNat round.toNat
  icases array_read _ (sint.Z (W64 0)) _ (encC (st.counts phase.toNat round.toNat))
    (W64 (st.counts phase.toNat round.toNat).1) (by decide) (by simp [encC]) $$ m with ⟨Hm0, m⟩
  wp_auto
  ihave m := m $$ Hm0
  icases array_read _ (sint.Z (W64 1)) _ (encC (st.counts phase.toNat round.toNat))
    (W64 (st.counts phase.toNat round.toNat).2.1) (by decide) (by simp [encC]) $$ m with ⟨Hm1, m⟩
  wp_auto
  ihave m := m $$ Hm1
  have e1 : sint.Z (W64 ((st.counts phase.toNat round.toNat).1 : Nat)) =
      ((st.counts phase.toNat round.toNat).1 : Int) := by unfold cntOk at hc1; word
  have e2 : sint.Z (W64 ((st.counts phase.toNat round.toNat).2.1 : Nat)) =
      ((st.counts phase.toNat round.toNat).2.1 : Int) := by unfold cntOk at hc2; word
  wp_if_destruct
  · rw [e1, e2] at Hif
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
        iframe Hdone Hrecv Hdec Hps Hpsl Hpscap Htl Hbs Hbsl Hbscap Hts Htsl Htscap Hdecrep
      · ipureintro; exact Hwf
    have hv : (st.counts phase.toNat round.toNat).majV = 0 := by
      unfold Counts.majV; rw [if_pos (by omega)]
    rw [hv]
    iapply HΦ
    itrivial
  · rw [e1, e2] at Hif
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
        iframe Hdone Hrecv Hdec Hps Hpsl Hpscap Htl Hbs Hbsl Hbscap Hts Htsl Htscap Hdecrep
      · ipureintro; exact Hwf
    have hv : (st.counts phase.toNat round.toNat).majV = 1 := by
      unfold Counts.majV; rw [if_neg (by omega)]
    rw [hv]
    iapply HΦ
    itrivial

end proof
end Perennial.rabia.internal.ledger
