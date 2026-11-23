/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__HasEnoughMsg.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).HasEnoughMsg`.
-/
module

public import Dsverify.Proof.rabia.internal.ledger.Slot__recvBCMsgsT

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

/-- `HasEnoughMsg` at a configuration `choose` can pick (`NMinusF` at most 4). -/
theorem Slot.HasEnoughMsg.wp_proof_ok (cf : RCfg) (hc : cf.Ok) (s : Loc) (γ : GName) (q : GoChan)
    (phase round : w32) (hr : round = 1 ∨ round = 2) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗ isSlot s γ q -∗
      rabia.internal.config.confRO cf -∗
      <<{ ∀∀ st, slotSt γ st }>>
        (App (App (Val (s @!! go.GoType.PointerType Slot.ty @!! go!"HasEnoughMsg"))
          (Val #phase)) (Val #round)) @ ∅
      <<{ slotSt γ st | RET #(decide (st.total phase.toNat round.toNat ≥ cf.q)); True }>> := by
  have hq := q_ok hc
  iintro #Hpkg #Hslot #Hconf
  ihave ⟨#Hsync, #Hsort, #Hmsg⟩ := ledgerDeps $$ Hpkg
  unfold isSlot
  icases Hslot with ⟨#Hq, #Ht, #Hm⟩
  icases rabia.internal.config.confRO_val $$ Hconf with ⟨%cps, #Hc⟩
  unfold atomic_wp
  iintro %Φ AU
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hm] as ⟨Hlocked, Hinv⟩
  iNamed Hinv
  ihave HΦ : |={⊤}=> (ghostVar γ (1 : Qp).half st ∗
      (True -∗ Φ #(decide (st.total phase.toNat round.toNat ≥ cf.q)))) $$ [AU Hγ]
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
  have hl : st.bcT.length < 2 ^ 32 := by
    obtain ⟨-, -, -, -, -, -, h7, h8⟩ := Hwf; omega
  wp_apply Slot.wp_recvBCMsgsT s ts st phase round hr hl $$ [$Hts $Htsl] as ⟨Hts, Htsl⟩
  ihave Hc2 := Hc
  iStructNamed Hc2
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
      iframe Hdone Hrecv Hdec Hps Hpsl Hpscap Htl Hbs Hbsl Hbscap Hts Htsl Htscap Hdecrep
    · ipureintro; exact Hwf
  have ht := st.wf_total_ok Hwf phase.toNat round.toNat
  have he : decide (sint.Z (W64 cf.q) ≤ sint.Z (W64 (st.total phase.toNat round.toNat : Nat))) =
      decide (st.total phase.toNat round.toNat ≥ cf.q) := by
    have h1 : sint.Z (W64 (st.total phase.toNat round.toNat : Nat)) =
        (st.total phase.toNat round.toNat : Int) := by unfold cntOk at ht; word
    rw [h1, show sint.Z (W64 cf.q) = (cf.q : Int) by word]
    exact decide_eq_decide.2 ⟨fun h => by omega, fun h => by omega⟩
  rw [he]
  iapply HΦ
  itrivial

theorem Slot.HasEnoughMsg.wp_proof : Slot.HasEnoughMsg.spec (GF := GF) :=
    fun cf s γ q phase round hr => by
  by_cases hc : cf.Ok
  · exact Slot.HasEnoughMsg.wp_proof_ok (GF := GF) cf hc s γ q phase round hr
  · -- `confRO cf` carries `cf.Ok` (H2-ledger-1)
    iintro - - Hc
    ihave %h := rabia.internal.config.confRO_ok cf $$ Hc
    exact absurd h hc

end proof
end Perennial.rabia.internal.ledger
