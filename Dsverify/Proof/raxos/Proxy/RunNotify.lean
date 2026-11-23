/-
Package `proxy`: `handleDecisionNotification` (`proxysmrhandler.go`): sends the decided slots to
piggyback (if any) to the proposer, then resets them.
-/
module

public import Dsverify.Proof.raxos.Proxy.RunDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

instance rn_decidedSlotsP_persistent (γ : QNames) (a b c : GoSlice) :
    Persistent (decidedSlotsP (GF := GF) γ a b c) := by
  unfold decidedSlotsP; infer_instance

/-- The empty decided slots. -/
theorem rn_decidedSlotsP_empty (γ : QNames) (a b c : GoSlice) :
    ⊢@{IProp GF} a ↦* ([] : List w64) -∗ b ↦* ([] : List w32) -∗ c ↦* ([] : List GoSlice) ==∗
      decidedSlotsP γ a b c := by
  iintro Ha Hb Hc
  imod (ownSlice_persist _ _ _) $$ Ha with Ha
  imod (ownSlice_persist _ _ _) $$ Hb with Hb
  imod (ownSlice_persist _ _ _) $$ Hc with Hc
  imodintro
  iunfold decidedSlotsP
  iexists [], [], [], []
  iframe Ha Hb Hc
  isplitr
  · ipureintro; simp
  iapply BigSepL.bigSepL_nil.2; iempintro

/-- Fresh, empty decided slots (the reset). -/
theorem rn_decState_reset (γ : QNames) (pr : Loc) (a b c : GoSlice) :
    ⊢@{IProp GF} pr.[Proxy, go!"lastDecidedIndexes"] ↦ a -∗
      pr.[Proxy, go!"lastDecidedProposers"] ↦ b -∗ pr.[Proxy, go!"lastDecidedDecisions"] ↦ c -∗
      a ↦* ([] : List w64) -∗ b ↦* ([] : List w32) -∗ c ↦* ([] : List GoSlice) -∗
      ownSliceCap w64 a (DFrac.own 1) -∗ ownSliceCap w32 b (DFrac.own 1) -∗
      ownSliceCap GoSlice c (DFrac.own 1) ==∗ decState γ pr := by
  iintro Hl Hp Hd Ha Hb Hc Hca Hcb Hcc
  imod (rn_decidedSlotsP_empty γ a b c) $$ Ha Hb Hc with #Hds
  imodintro
  iunfold decState
  iexists a, b, c
  iframe
  iexact Hds

theorem wp_handleDecisionNotification : handleDecisionNotification_spec (GF := GF) (hG := hG) := by
  intro γ pr
  wp_start as ⟨#Hch, Hds⟩
  iunfold chanField at Hch
  icases Hch with ⟨%ch, %γc, #Hchf, #Hbag⟩
  iunfold decState at Hds
  icases Hds with ⟨%ls, %ps, %ds, Hl, Hp, Hd, #Hsl, Hca, Hcb, Hcc⟩
  ihave #Hsl' := Hsl
  iunfold decidedSlotsP at Hsl'
  icases Hsl' with ⟨%is, %pps, %dsls, %dds, #His, #Hps, #Hdsl, %Hlens, #Hel⟩
  ihave %Hilen := ownSlice_len _ _ _ $$ His
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iunfold decState
    iexists ls, ps, ds
    iframe
    iframe #
  · wp_apply wp_bag_send $$ [Hbag]
    · iframe Hbag
      iunfold decisionP
      dsimp only
      isplitl []
      · iexact Hsl
      · ipureintro; word
    wp_apply (wp_slice_make2 (V := w64)) as %a ⟨Ha, Hcap_a⟩
    · ipureintro; word
    wp_apply (wp_slice_make2 (V := w32)) as %b ⟨Hb, Hcap_b⟩
    · ipureintro; word
    wp_apply +noauto (wp_slice_make2 (V := GoSlice)) as %c ⟨Hc, Hcap_c⟩
    · ipureintro; word
    simp only [List.replicate_zero]
    imod (rn_decidedSlotsP_empty γ a b c) $$ Ha Hb Hc with #Hds
    wp_auto
    iapply HΦ
    iunfold decState
    iexists a, b, c
    iframe
    iexact Hds

end proofs

end Perennial.raxos
