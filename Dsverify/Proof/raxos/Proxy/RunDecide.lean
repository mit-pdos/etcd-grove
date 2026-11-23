/-
Package `proxy`: `handleProposeResponse` (`proxysmrhandler.go`): a decision of a slot this proxy
proposed (so in its log) is recorded, the proposed ids put back if another value was decided, the
decided ids removed from `toBeProposed`; the state machine is updated (answering the clients);
the slot is piggybacked on the next proposal.
-/
module

public import Dsverify.Proof.raxos.Proxy.RunDecideGhost
public import Dsverify.Proof.raxos.Proxy.RunSmrCode
public import Dsverify.Proof.raxos.Proxy.RunRemove

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
variable [ha : hyp.AtoiSpec GF]

attribute [local instance] HeapGS.goose_globalGS

theorem wp_handleProposeResponse
    (wp_uet : updateEpochTime_spec (GF := GF) (hG := hG)) :
    handleProposeResponse_spec (GF := GF) (hG := hG) := by
  intro γ cf k pr γq m
  wp_start as ⟨#Hsh, Hown, Hm⟩
  iunfold proposeRespP at Hm
  icases Hm with ⟨%ids, %ids0, #Hdecs, #Hdec, %lead, #Hinit⟩
  wp_auto
  wp_if_destruct
  · iapply HΦ; iexact Hown
  wp_if_destruct
  · iapply HΦ; iexact Hown
  ihave Hsh' := Hsh
  iunfold proxySharedDef at Hsh'
  icases Hsh' with ⟨%_hs, %_γs', %_cb', %_bm', %_ebm', #Hfacts, #Hconsts, -, #Hchans, -, -⟩
  iunfold sharedFacts at Hfacts
  icases Hfacts with ⟨%Hk, #Hcons, #Hsmri, -, #Hnilreg, -⟩
  have Hok0 := Hk.1
  iunfold ownQ at Hown
  icases Hown with ⟨%γs, %cb, %bm, %ebm, %rl, %slots, %L, %c, %lp, %D, %Bm, %tb, %tbs, #Hcb, #Hst,
    #Hnil, #Hbm, #Hebm, Hrl, Hsl, Hcap, Hlog, Hsmr, Hlp, Hfront, %Hlpb, Htbf, Htb, Htbcap, #Hids,
    Hdecst, Hepo, Hprop⟩
  iunfold ownProp at Hprop
  icases Hprop with ⟨%Pm, %its, %ts, %tlp, %bt, #Hch, Hauth, Htoks, %HPm, Hits, Hts, %Hts, Htlp,
    #Hbt⟩
  imod (rd_init_in_log γ ⊤ CoPset.subseteq_top k Pm (sint.Z lp) slots.length (sint.Z m.index') ids0
    lead HPm.2) $$ Hcons Hinit Hfront Htoks with ⟨Hfront, Htoks, %Hidx⟩
  imod (rd_decided_ok γ ⊤ CoPset.subseteq_top _ ids) $$ Hcons Hdec with %Hok
  ihave %Hrllen := ownSlice_len $$ Hsl
  ihave #Husm := usmShared_of γ cf k pr γs cb bm ebm $$ Hsh Hcb Hst Hbm Hebm
  list_elem slots (sint.nat m.index') as s
  have Hb : 0 ≤ sint.Z m.index' ∧ sint.Z m.index' < sint.Z rl.len := ⟨by omega, by word⟩
  have hs' : slots[(sint.Z m.index').toNat]? = some s := by simpa using Hs_lookup
  icases ownSlice_elem_acc (sint.Z m.index') s rl _ slots (by omega) hs' $$ Hsl with ⟨Hel, Hsl⟩
  repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
  iunfold logP at Hlog
  icases Hlog with ⟨%HLl, Hlog⟩
  ihave Hlog : logP γ γs cf slots L $$ [Hlog]
  · iunfold logP; iframe Hlog; ipureintro; exact HLl
  have Hi0 : 0 ≤ sint.Z m.index' := by omega
  have HiN : (sint.Z m.index').toNat < slots.length := by omega
  ipersist pr
  wp_join iprop(∃ (slots' : List Slot) (L' : List (Option (List GoString))),
      pr.[Proxy, go!"replicatedLog"] ↦ rl ∗ rl ↦* slots' ∗ logP γ γs cf slots' L' ∗
      smrP γ pr bm ebm L' c D Bm ∗ rd_tbP γ γs pr ∗ ⌜L'.length = slots.length⌝ ∗ message_ptr ↦ m ∗
      epochOwn pr)
    with [Hrl Hel Hsl Hlog Hsmr Htbf Htb Htbcap message Hepo]
    as ⟨%slots', %L', Hrl, Hsl, Hlog, Hsmr, Htbp, %HL', message, Hepo⟩
  · -- not decided yet: record the decision
    icases rd_log_acc γ γs cf slots L _ s hs' $$ Hlog with ⟨%o, %Ho, Hslot, Hlogw⟩
    iunfold slotP at Hslot
    icases Hslot with ⟨%Hdec, Hslot⟩
    rcases o with _ | ids'
    case some => simp at Hdec; rw [Hdec] at Hif; exact absurd Hif (by decide)
    icases Hslot with ⟨%pids, #Hpids, #Hpidsok⟩
    ihave Htbp : rd_tbP γ γs pr $$ [Htbf Htb Htbcap]
    · iunfold rd_tbP; iexists tb, tbs; iframe Htbf Htb Htbcap Hids
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    ihave Hsl := Hsl $$ Hel
    wp_apply (wp_uet cf k pr m.index' rl _) $$ [Hepo Hrl Hsl] as ⟨Hepo, Hrl, Hsl⟩
    · iframe #; iframe; ipureintro; exact ⟨Hok0, by omega, by omega⟩
    have HiN' : (slots.set (sint.Z m.index').toNat
        (Slot.mk s.proposedBatch' m.decisions' true s.committed' m.proposer' m.s'))[(sint.Z m.index').toNat]? =
        some (Slot.mk s.proposedBatch' m.decisions' true s.committed' m.proposer' m.s') :=
      List.getElem?_set_self HiN
    wp_apply (rd_wp_decidedTheProposedValue pr rl (slots.set (sint.Z m.index').toNat
        (Slot.mk s.proposedBatch' m.decisions' true s.committed' m.proposer' m.s')) m.index'
      (Slot.mk s.proposedBatch' m.decisions' true s.committed' m.proposer' m.s') pids m.decisions' ids
      Hi0 HiN') $$ [Hrl Hsl] as %b ⟨Hrl, Hsl⟩
    · iframe Hrl Hpids Hdecs
      iexact Hsl
    wp_join iprop(∃ (s2 : Slot), pr.[Proxy, go!"replicatedLog"] ↦ rl ∗
        rl ↦* slots.set (sint.Z m.index').toNat s2 ∗
        ⌜s2.decided' = true ∧ s2.decidedBatch' = m.decisions'⌝ ∗ rd_tbP γ γs pr ∗ message_ptr ↦ m)
      at next with [Hrl Hsl Htbp message] as ⟨%s2, Hrl, Hsl, %Hs2, Htbp, message⟩
    cases b
    · -- another value was decided: the proposed ids are put back (Q7: but a summary)
      have e : (((sint.Z m.index').toNat : Nat) : Int) = sint.Z m.index' := Int.toNat_of_nonneg Hi0
      wp_auto
      wp_apply (rd_wp_putBack γ γs cf k pr rl _ m.index' _ pids Hok0 ⟨Hi0, by omega⟩ HiN')
        $$ [Hrl Hsl Htbp] as ⟨Hrl, Hsl, Htbp⟩
      · iframe #; iframe; rw [e]; iexact Hpidsok
      icases ownSlice_elem_acc (sint.Z m.index') _ rl _ _ Hi0 HiN' $$ Hsl
        with ⟨Hel, Hsl⟩
      repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
      ihave Hsl := Hsl $$ Hel
      rw [List.set_set]
      isplitl []
      · itrivial
      iexists _
      iframe Hrl Hsl message
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iexact Htbp
    · wp_auto
      isplitl []
      · itrivial
      iexists _
      iframe Hrl Hsl Htbp message
      ipureintro; exact ⟨rfl, rfl⟩
    have hs2 : (slots.set (sint.Z m.index').toNat s2)[(sint.Z m.index').toNat]? = some s2 :=
      List.getElem?_set_self HiN
    icases ownSlice_elem_acc (sint.Z m.index') s2 rl _ _ Hi0 hs2 $$ Hsl with ⟨Hel, Hsl⟩
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    ihave Hsl := Hsl $$ Hel
    rw [list_set_lookup_self _ _ _ hs2, Hs2.2]
    wp_apply rd_wp_removeDecided γ γs pr m.decisions' ids $$ [$Htbp $Hdecs] as Htbp
    isplitl []
    · itrivial
    iexists slots.set (sint.Z m.index').toNat s2, L.set (sint.Z m.index').toNat (some ids)
    iframe Hrl Hsl message Htbp
    isplitl [Hlogw]
    · iapply Hlogw
      iunfold slotP
      isplitr
      · ipureintro; simp [Hs2.1]
      dsimp only
      rw [Hs2.2]
      iframe Hdecs
      isplitr
      · ipureintro; exact ⟨Hok.1, Hok.2.1⟩
      have hn0 : ¬ (sint.Z m.index').toNat = 0 := by omega
      simp only [hn0, ↓reduceIte]
      rw [Int.toNat_of_nonneg Hi0]
      iexact Hdec
    isplitl [Hsmr]
    · iapply rd_smrP_set γ pr bm ebm L c D Bm _ (some ids) Ho (by omega) $$ Hsmr
    iframe Hepo
    ipureintro; simp [HLl]
  · ihave Hsl := Hsl $$ Hel
    rw [list_set_lookup_self _ _ _ hs']
    iexists slots, L
    iframe Hrl Hsl Hlog Hsmr
    isplitl [Htbf Htb Htbcap]
    · iunfold rd_tbP; iexists tb, tbs; iframe Htbf Htb Htbcap Hids
    iframe message Hepo
    ipureintro; exact HLl.symm
  wp_apply (wp_updateStateMachine γ γs cf pr cb bm ebm true rl slots' L' c D Bm) $$ [Hrl Hsl Hlog Hsmr]
    as ⟨%slots'', %c', %D', %Bm', Hrl, Hsl, Hlog, Hsmr⟩
  · iframe Husm Hrl Hsl Hlog Hsmr
  iunfold decState at Hdecst
  icases Hdecst with ⟨%ls, %ps, %ds, Hls, Hps, Hds, Hdsp, Hlcap, Hpcap, Hdcap⟩
  iunfold decidedSlotsP at Hdsp
  icases Hdsp with ⟨%is, %prs, %dsls, %dss, #His, #Hprs, #Hdsls, %Hlens, #Hall⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.int) [m.index']
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit1 ⟨Hlit1, -⟩
  wp_apply (wp_slice_append_dfrac (V := w64) ls is DFrac.discard _ [m.index'] (DFrac.own 1))
    $$ [$His $Hlcap $Hlit1] as %ls' ⟨His', Hlcap, -⟩
  · ipureintro; exact DFrac.valid_discard
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int32)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w32) (t := go.int32) [m.proposer']
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit2 ⟨Hlit2, -⟩
  wp_apply (wp_slice_append_dfrac (V := w32) ps prs DFrac.discard _ [m.proposer'] (DFrac.own 1))
    $$ [$Hprs $Hpcap $Hlit2] as %ps' ⟨Hprs', Hpcap, -⟩
  · ipureintro; exact DFrac.valid_discard
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType (go.GoType.SliceType go.string)))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoSlice) (t := go.GoType.SliceType go.string) [m.decisions']
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit3 ⟨Hlit3, -⟩
  wp_apply (wp_slice_append_dfrac (V := GoSlice) ds dsls DFrac.discard _ [m.decisions'] (DFrac.own 1))
    $$ [$Hdsls $Hdcap $Hlit3] as %ds' ⟨Hdsls', Hdcap, -⟩
  · ipureintro; exact DFrac.valid_discard
  iunfold logP at Hlog
  icases Hlog with ⟨%HLl'', Hlog⟩
  ihave Hlog : logP γ γs cf slots'' L' $$ [Hlog]
  · iunfold logP; iframe Hlog; ipureintro; exact HLl''
  have Hn : slots''.length = slots.length := by rw [HLl'', HL']
  iunfold rd_tbP at Htbp
  icases Htbp with ⟨%tb2, %tbs2, Htbf, Htb, Htbcap, #Hids2⟩
  iapply HΦ
  iunfold ownQ
  iexists γs, cb, bm, ebm, rl, slots'', L', c', lp, D', Bm', tb2, tbs2
  iframe Hcb Hst Hnil Hbm Hebm Hrl Hsl Hcap Hlog Hsmr Hlp Htbf Htb Htbcap Hids2
  rw [Hn]
  iframe Hfront
  isplitr
  · ipureintro; exact Hlpb
  isplitr [Hch Hauth Htoks Hits Hts Htlp Hepo]
  · iunfold decState
    iexists ls', ps', ds'
    iframe Hls Hps Hds Hlcap Hpcap Hdcap
    iunfold decidedSlotsP
    iexists is ++ [m.index'], prs ++ [m.proposer'], dsls ++ [m.decisions'], dss ++ [ids]
    iframe His' Hprs' Hdsls'
    isplitr
    · ipureintro; simp [Hlens.1, Hlens.2.1, Hlens.2.2]
    iapply BigSepL.bigSepL_snoc.2
    isplitl []
    · iapply BigSepL.bigSepL_impl $$ Hall
      imodintro
      iintro %j %d %Hj ⟨%sl, %i, %Hsi, Hsl1, Hd1⟩
      iexists sl, i
      iframe Hsl1 Hd1
      ipureintro
      have hj : j < dss.length := (List.getElem?_eq_some_iff.1 Hj).1
      refine ⟨?_, ?_, Hsi.2.2⟩
      · rw [List.getElem?_append_left (by omega)]; exact Hsi.1
      · rw [List.getElem?_append_left (by omega)]; exact Hsi.2.1
    iexists m.decisions', m.index'
    iframe Hdecs Hdec
    ipureintro
    refine ⟨?_, ?_, Hok.2.1⟩
    · rw [← Hlens.2.2]; simp
    · rw [← Hlens.1]; simp
  iframe Hepo
  iunfold ownProp
  iexists Pm, its, ts, tlp, bt
  iframe Hch Hauth Htoks Hits Hts Htlp Hbt
  ipureintro; exact ⟨HPm, Hts⟩

end proofs

end Perennial.raxos
