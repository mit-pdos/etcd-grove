/-
Package `proxy`: `handleRecorderResponse` (`proxysmrhandler.go`): decisions from the local
recorder; the log is extended up to the highest decided slot, each undecided slot among them
recorded (the proposed ids put back if another value was decided, the decided ids removed from
`toBeProposed`), and the state machine updated.
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

theorem wp_handleRecorderResponse
    (wp_uet : updateEpochTime_spec (GF := GF) (hG := hG)) :
    handleRecorderResponse_spec (GF := GF) (hG := hG) := by
  intro γ cf k pr γq m
  wp_start as ⟨#Hsh, Hown, Hm⟩
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
  ihave #Husm := usmShared_of γ cf k pr γs cb bm ebm $$ Hsh Hcb Hst Hbm Hebm
  iunfold decisionP at Hm
  icases Hm with ⟨Hm, %Hipos⟩
  iunfold decidedSlotsP at Hm
  icases Hm with ⟨%is, %prs, %dsls, %dss, #His, #Hprs, #Hdsls, %Hlens, #Hall⟩
  ihave %Hisl := ownSlice_len $$ His
  ihave %Hprsl := ownSlice_len $$ Hprs
  ihave %Hdsl := ownSlice_len $$ Hdsls
  ihave %Hdl := ownSlice_len $$ Hsl
  iunfold logP at Hlog
  icases Hlog with ⟨%HLl, Hlog⟩
  ihave Hlog : logP γ γs cf slots L $$ [Hlog]
  · iunfold logP; iframe Hlog; ipureintro; exact HLl
  wp_auto
  have Hleq : m.indexes'.len = m.decisions'.len := by word
  simp only [Hleq, decide_true, Bool.not_true]
  wp_auto
  have hne : is ≠ [] := by
    intro h; have h1 := Hisl.1; rw [h, List.length_nil] at h1
    have h2 : sint.nat m.indexes'.len = (sint.Z m.indexes'.len).toNat := rfl
    omega
  clear Hipos
  wp_apply rd_wp_getHighestIndex pr m.indexes' is hne $$ [$His] as %h %Hh
  -- the highest slot is decided: in [1, 72]
  obtain ⟨kh, Hkh⟩ := List.mem_iff_getElem?.1 Hh.1
  have Hkd : kh < dss.length := by have := (List.getElem?_eq_some_iff.1 Hkh).1; omega
  list_elem dss kh as dh
  ihave Hentry := BigSepL.bigSepL_lookup Hdh_lookup $$ Hall
  icases Hentry with ⟨%slh, %ih, %Hih, -, #Hdech⟩
  have Hih' : ih = h := by rw [Hih.2.1] at Hkh; exact Option.some.inj Hkh
  subst Hih'
  imod (rd_decided_ok γ ⊤ CoPset.subseteq_top _ dh) $$ Hcons Hdech with %Hokh
  -- extend the log up to the highest slot
  ihave HE : (∃ (rl' : GoSlice) (slots' : List Slot) (L' : List (Option (List GoString))),
      "Hrl" ∷ pr.[Proxy, go!"replicatedLog"] ↦ rl' ∗ "Hsl" ∷ rl' ↦* slots' ∗
      "Hcap" ∷ ownSliceCap Slot rl' (DFrac.own 1) ∗ "Hlog" ∷ logP γ γs cf slots' L' ∗
      "Hsmr" ∷ smrP γ pr bm ebm L' c D Bm ∗
      "%HE" ∷ ⌜slots.length ≤ slots'.length ∧ (slots'.length ≤ slots.length ∨
        slots'.length ≤ sint.Z ih + 1) ∧ slots'.length = L'.length⌝ : IProp GF)
    $$ [Hrl Hsl Hcap Hlog Hsmr]
  · iexists rl, slots, L; iframe; ipureintro; omega
  wp_for HE
  wp_loop_if
  · ihave %Hsl' := ownSlice_len $$ Hsl
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType Slot.ty)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Slot) (t := Slot.ty) [rd_emptySlot]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply (wp_slice_append (V := Slot) rl' slots' _ [rd_emptySlot] (DFrac.own 1))
      $$ [$Hsl $Hcap $Hlit] as %rl'' ⟨Hsl, Hcap, -⟩
    ihave Hlog := rd_log_snoc γ γs cf slots' L' rd_emptySlot ⟨rfl, rfl⟩ $$ Hlog
    ihave Hsmr := rd_smrP_snoc γ pr bm ebm L' c D Bm (by word) $$ Hsmr
    wp_for_post
    iframe
    iexists rl'', slots' ++ [rd_emptySlot], L' ++ [none]
    iframe
    ipureintro
    simp only [List.length_append, List.length_singleton]
    refine ⟨by omega, ?_, by omega⟩
    right; word
  -- record each decision
  ihave %Hsl' := ownSlice_len $$ Hsl
  have Hn1 : sint.Z ih + 1 ≤ slots'.length := by
    have := Hif; rw [show sint.Z (ih + W64 1) = sint.Z ih + 1 by word] at this
    rw [Hsl'.1]; word
  ihave Htbp : rd_tbP γ γs pr $$ [Htbf Htb Htbcap]
  · iunfold rd_tbP; iexists tb, tbs; iframe Htbf Htb Htbcap Hids
  ihave HM : (∃ (i : w64) (slots2 : List Slot) (L2 : List (Option (List GoString))),
      "i" ∷ i_ptr ↦ i ∗ "Hrl" ∷ pr.[Proxy, go!"replicatedLog"] ↦ rl' ∗ "Hsl" ∷ rl' ↦* slots2 ∗
      "Hlog" ∷ logP γ γs cf slots2 L2 ∗ "Hsmr" ∷ smrP γ pr bm ebm L2 c D Bm ∗ "Htbp" ∷ rd_tbP γ γs pr ∗
      "Hepo" ∷ epochOwn pr ∗
      "%HM" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z m.indexes'.len ∧ slots2.length = slots'.length ∧
        L2.length = slots'.length⌝ : IProp GF) $$ [i Hrl Hsl Hlog Hsmr Htbp Hepo]
  · iexists W64 0, slots', L'; iframe; ipureintro; refine ⟨by word, by word, rfl, HE.2.2.symm⟩
  wp_for HM
  wp_loop_if
  · have Hlt : sint.nat i < is.length := by word
    list_elem is (sint.nat i) as ix
    list_elem dss (sint.nat i) as d
    list_elem dsls (sint.nat i) as sl
    list_elem prs (sint.nat i) as p
    ihave Hen := BigSepL.bigSepL_lookup Hd_lookup $$ Hall
    icases Hen with ⟨%sl', %ix', %Hsx, #Hsld, #Hdecd⟩
    have Hix : ix' = ix := by rw [Hsx.2.1] at Hix_lookup; exact Option.some.inj Hix_lookup
    have Hsl'' : sl' = sl := by rw [Hsx.1] at Hsl_lookup; exact Option.some.inj Hsl_lookup
    subst Hix Hsl''
    imod (rd_decided_ok γ ⊤ CoPset.subseteq_top _ d) $$ Hcons Hdecd with %Hokd
    ihave %Hsll := ownSlice_len $$ Hsld
    have Hixh : sint.Z ix' ≤ sint.Z ih := Hh.2 ix' (List.mem_of_getElem? Hix_lookup)
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z m.indexes'.len := ⟨HM.1, Hif⟩
    have Hbd : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z m.decisions'.len := ⟨HM.1, by word⟩
    have Hbp : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z m.proposers'.len := ⟨HM.1, by word⟩
    repeat' (first | wp_auto | simp only [Hb, Hbd, Hbp, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index m.indexes' (sint.Z i) is _ ix' HM.1 $$ [$His] as -
    · ipureintro; simpa using Hix_lookup
    repeat' (first | wp_auto | simp only [Hb, Hbd, Hbp, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index m.decisions' (sint.Z i) dsls _ sl' HM.1 $$ [$Hdsls] as -
    · ipureintro; simpa using Hsl_lookup
    repeat' (first | wp_auto | simp only [Hb, Hbd, Hbp, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index m.proposers' (sint.Z i) prs _ p HM.1 $$ [$Hprs] as -
    · ipureintro; simpa using Hp_lookup
    have Hne0 : ¬ sl'.len = W64 0 := by
      intro h0; apply Hokd.1; apply List.eq_nil_of_length_eq_zero; rw [Hsll.1, h0]; rfl
    simp only [Hne0, decide_false, ↓reduceIte]
    wp_auto
    -- the slot
    have Hi0 : 0 ≤ sint.Z ix' := by omega
    have HiN : (sint.Z ix').toNat < slots2.length := by omega
    list_elem slots2 (sint.Z ix').toNat as s
    have HbS : 0 ≤ sint.Z ix' ∧ sint.Z ix' < sint.Z rl'.len := ⟨Hi0, by word⟩
    icases ownSlice_elem_acc (sint.Z ix') s rl' _ slots2 Hi0 Hs_lookup $$ Hsl with ⟨Hel, Hsl⟩
    ipersist index
    ipersist batches
    ipersist proposer
    repeat' (first | wp_auto | simp only [HbS, _root_.and_self, ↓reduceIte])
    wp_if_destruct
    · -- not decided yet: record the decision
      icases rd_log_acc γ γs cf slots2 L2 _ s Hs_lookup $$ Hlog with ⟨%o, %Ho, Hslot, Hlogw⟩
      iunfold slotP at Hslot
      icases Hslot with ⟨%Hdec, Hslot⟩
      rcases o with _ | ids'
      case some => simp at Hdec; rw [Hdec] at Hif; exact absurd Hif (by decide)
      icases Hslot with ⟨%pids, #Hpids, #Hpidsok⟩
      repeat' (first | wp_auto | simp only [HbS, _root_.and_self, ↓reduceIte])
      ihave Hsl := Hsl $$ Hel
      wp_apply (wp_uet cf k pr ix' rl' _) $$ [Hepo Hrl Hsl] as ⟨Hepo, Hrl, Hsl⟩
      · iframe #; iframe; ipureintro; exact ⟨Hok0, by omega, by omega⟩
      have HiN' : (slots2.set (sint.Z ix').toNat
          (Slot.mk s.proposedBatch' sl' true s.committed' p s.s'))[(sint.Z ix').toNat]? =
          some (Slot.mk s.proposedBatch' sl' true s.committed' p s.s') :=
        List.getElem?_set_self HiN
      wp_apply (rd_wp_decidedTheProposedValue pr rl' (slots2.set (sint.Z ix').toNat
          (Slot.mk s.proposedBatch' sl' true s.committed' p s.s')) ix'
        (Slot.mk s.proposedBatch' sl' true s.committed' p s.s') pids sl' d
        Hi0 HiN') $$ [Hrl Hsl] as %b ⟨Hrl, Hsl⟩
      · iframe Hrl Hpids Hsld
        iexact Hsl
      wp_join iprop(∃ (s2 : Slot), pr.[Proxy, go!"replicatedLog"] ↦ rl' ∗
          rl' ↦* slots2.set (sint.Z ix').toNat s2 ∗
          ⌜s2.decided' = true ∧ s2.decidedBatch' = sl'⌝ ∗ rd_tbP γ γs pr ∗ pr_ptr ↦ pr)
        at next with [Hrl Hsl Htbp pr] as ⟨%s2, Hrl, Hsl, %Hs2, Htbp, pr⟩
      cases b
      · have e : (((sint.Z ix').toNat : Nat) : Int) = sint.Z ix' := Int.toNat_of_nonneg Hi0
        wp_auto
        wp_apply (rd_wp_putBack γ γs cf k pr rl' _ ix' _ pids Hok0 ⟨Hi0, by omega⟩ HiN')
          $$ [Hrl Hsl Htbp] as ⟨Hrl, Hsl, Htbp⟩
        · iframe #; iframe; rw [e]; iexact Hpidsok
        icases ownSlice_elem_acc (sint.Z ix') _ rl' _ _ Hi0 HiN' $$ Hsl with ⟨Hel, Hsl⟩
        repeat' (first | wp_auto | simp only [HbS, _root_.and_self, ↓reduceIte])
        ihave Hsl := Hsl $$ Hel
        rw [List.set_set]
        isplitl []
        · itrivial
        iexists _
        iframe Hrl Hsl pr
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        iexact Htbp
      · wp_auto
        isplitl []
        · itrivial
        iexists _
        iframe Hrl Hsl Htbp pr
        ipureintro; exact ⟨rfl, rfl⟩
      wp_apply rd_wp_removeDecided γ γs pr sl' d $$ [$Htbp $Hsld] as Htbp
      ihave Hlog := Hlogw $$ %s2 %(some d) []
      · iunfold slotP
        isplitr
        · ipureintro; simp [Hs2.1]
        dsimp only
        rw [Hs2.2]
        iframe Hsld
        isplitr
        · ipureintro; exact ⟨Hokd.1, Hokd.2.1⟩
        have hn0 : ¬ (sint.Z ix').toNat = 0 := by omega
        simp only [hn0, ↓reduceIte]
        rw [Int.toNat_of_nonneg Hi0]
        iexact Hdecd
      ihave Hsmr := rd_smrP_set γ pr bm ebm L2 c D Bm _ (some d) Ho (by omega) $$ Hsmr
      wp_for_post
      iframe
      iexists i + W64 1, slots2.set (sint.Z ix').toNat s2, L2.set (sint.Z ix').toNat (some d)
      iframe
      ipureintro
      refine ⟨by word, by word, by simp [HM.2.2.1], by simp [HM.2.2.2]⟩
    · -- decided already
      ihave Hsl := Hsl $$ Hel
      rw [list_set_lookup_self _ _ _ Hs_lookup]
      wp_for_post
      iframe
      iexists i + W64 1, slots2, L2
      iframe
      ipureintro; exact ⟨by word, by word, HM.2.2.1, HM.2.2.2⟩
  · wp_apply (wp_updateStateMachine γ γs cf pr cb bm ebm false rl' slots2 L2 c D Bm)
      $$ [Hrl Hsl Hlog Hsmr] as ⟨%slots'', %c', %D', %Bm', Hrl, Hsl, Hlog, Hsmr⟩
    · iframe Husm Hrl Hsl Hlog Hsmr
    iunfold logP at Hlog
    icases Hlog with ⟨%HLl'', Hlog⟩
    ihave Hlog : logP γ γs cf slots'' L2 $$ [Hlog]
    · iunfold logP; iframe Hlog; ipureintro; exact HLl''
    have Hn : slots''.length = slots'.length := by rw [HLl'', HM.2.2.2]
    iunfold rd_tbP at Htbp
    icases Htbp with ⟨%tb2, %tbs2, Htbf, Htb, Htbcap, #Hids2⟩
    iunfold ownProp at Hprop
    icases Hprop with ⟨%Pm, %its, %ts, %tlp, %bt, #Hch, Hauth, Htoks, %HPm, Hits, Hts, %Hts, Htlp,
      #Hbt⟩
    iapply HΦ
    iunfold ownQ
    iexists γs, cb, bm, ebm, rl', slots'', L2, c', lp, D', Bm', tb2, tbs2
    iframe Hcb Hst Hnil Hbm Hebm Hrl Hsl Hcap Hlog Hsmr Hlp Htbf Htb Htbcap Hids2 Hfront Hdecst Hepo
    isplitr
    · ipureintro; exact Hlpb
    iunfold ownProp
    iexists Pm, its, ts, tlp, bt
    iframe Hch Hauth Htoks Hits Hts Htlp Hbt
    ipureintro
    refine ⟨⟨HPm.1, fun j h1 h2 => ?_⟩, Hts⟩
    rcases HPm.2 j h1 h2 with h | h
    · left; rw [Hn]; omega
    · right; exact h

end proofs

end Perennial.raxos
