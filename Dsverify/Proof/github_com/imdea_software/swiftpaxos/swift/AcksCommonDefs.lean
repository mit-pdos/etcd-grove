/-
The definitions, specs and lemmas of `AcksCommon.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcksSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.LeaderM
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.PoolFnsDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The leader's id as `leader()` computes it is the model's `leaderOf`. -/
theorem swift.rid_leader (bw : w32) (N b : Nat) (hN : 1 ≤ N ∧ N ≤ 7) (hb : sp.bal bw = b)
    (hpos : 0 ≤ sint.Z bw) :
    sp.rid (BitVec.srem bw (W32 (sint.Z (W64 (N : Int))))) = sp.leaderOf N b := by
  have hv := replica.quorum.leader_val bw N (by omega) hpos
  have hN' : sint.Z (W64 (N : Int)) = N := by word
  rw [← hb]
  unfold sp.rid sp.bal sp.leaderOf
  rw [hN']
  have hv' : (BitVec.srem bw (W32 (N : Int))).toInt = bw.toInt % (N : Int) := hv
  rw [hv', Int.toNat_emod hpos (by omega)]
  simp

/-- A replica id that is not `leader()`'s (both non-negative) is not the model's leader. -/
theorem swift.rid_ne_leader (me bw : w32) (N b : Nat) (hN : 1 ≤ N ∧ N ≤ 7) (hb : sp.bal bw = b)
    (hpos : 0 ≤ sint.Z bw) (hme : 0 ≤ sint.Z me)
    (hne : me ≠ BitVec.srem bw (W32 (sint.Z (W64 (N : Int))))) :
    sp.rid me ≠ sp.leaderOf N b := by
  intro h
  apply hne
  rw [← swift.rid_leader bw N b hN hb hpos] at h
  have hv := replica.quorum.leader_val bw N (by omega) hpos
  have hN' : sint.Z (W64 (N : Int)) = N := by word
  have hl0 : 0 ≤ sint.Z (BitVec.srem bw (W32 (sint.Z (W64 (N : Int))))) := by
    rw [hN']; have : (BitVec.srem bw (W32 (N : Int))).toInt = bw.toInt % (N : Int) := hv
    show 0 ≤ (BitVec.srem bw (W32 (N : Int))).toInt
    rw [this]; exact Int.emod_nonneg _ (by omega)
  unfold sp.rid at h
  apply BitVec.eq_of_toInt_eq
  have := congrArg (fun n : Nat => (n : Int)) h
  simp only [Int.toNat_of_nonneg hme, Int.toNat_of_nonneg hl0] at this
  exact this

section c16
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- **C16, the producer side**: a light slow ack a replica sends (`fastAckFromLeader`: after its
acceptance of `x` in the ack's ballot, only when `r.leader() != r.Id`, the ballot being the
message's) has its strengthened witness. -/
theorem swift.lightSlowAckOk_intro (γ : sp.Names) (γc γm : GName) (N : Nat) (fr : Bool)
    (l : List GoString) (me bw : w32) (x : sp.CmdId) (hw : sp.wireOk me bw)
    (hnl : sp.rid me ≠ sp.leaderOf N (sp.bal bw)) :
    sp.cfg γc γm N fr l ∗ sp.accepted γ (sp.rid me) (sp.bal bw) x ⊢
      sp.msgOk γ γc γm (.lightSlowAck ⟨me, bw, x⟩) := by
  iintro ⟨#Hcfg, #Hacc⟩
  simp only [sp.msgOk]
  iframe Hacc
  isplitr
  · ipureintro; exact hw
  iexists N, fr, l
  iframe Hcfg
  ipureintro; exact hnl

/-- The strengthened witness's consequence (C16): the sender is not the ballot's leader. -/
theorem swift.lightSlowAckOk_notLeader (γ : sp.Names) (γc γm : GName) (N : Nat) (fr : Bool)
    (l : List GoString) (s : sp.SlowAck) :
    sp.cfg γc γm N fr l ∗ sp.msgOk γ γc γm (.lightSlowAck s) ⊢
      ⌜sp.rid s.rep ≠ sp.leaderOf N (sp.bal s.bal)⌝ := by
  simp only [sp.msgOk]
  iintro ⟨#Hcfg, ⟨-, -, %N', %fr', %l', #Hcfg', %Hne⟩⟩
  ihave %Hag := sp.cfg_agree (γc := γc) (γm := γm) N N' fr fr' l l' $$ [Hcfg Hcfg']
  · iframe Hcfg Hcfg'
  obtain ⟨rfl, -, -⟩ := Hag
  ipureintro; exact Hne

end c16

set_option hygiene false in
/-- `shOwn` back from its unpacked parts `Hshe`, `Hst` (value `st`), `HfqS` (round 24). -/
macro "shPack" : tactic => `(tactic| (
  ihave Hsh : swift.shOwn c d b qe $$ [Hshe Hst HfqS]
  · iunfold swift.shOwn; iframe Hshe; iunfold swift.shOwnR; iframe HfqS; iexists st; iexact Hst))

set_option hygiene false in
/-- `descOwn` back from its unpacked parts (the names of `commonCaseFastAck.wp_proof`). -/
macro "repackOwn" : tactic => `(tactic| (
  shPack
  iunfold swift.descOwn
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe HhS HhF HdS
  iunfold swift.setR
  iunfold swift.descSt
  iexists qe, bw, stp, rcp, dv, rv
  iframe Hsh HRC Hd Htok Hcom Hra HsF HfF HdF HDo Hpw Hdw HsB
  isplitl [Hbal HStf Hrcf Het Hxe]
  · iunfold swift.epochRd; iframe Hbal HStf Hrcf Het Hxe; ipureintro; exact Hbw
  isplitr
  · ipureintro; exact Hph
  ipureintro; exact Hrp))

set_option hygiene false in
/-- The message condition of `Add` for the ack at `l` (leader or not). -/
macro "ackCond" : tactic => `(tactic| (
  by_cases hld : fa.Replica' = BitVec.srem bw' (W32 (sint.Z (W64 (c.N : Int))))
  · rw [decide_eq_true hld]
    simp only [↓reduceIte]
    -- round B1 (D81): the leader branch is refuted by the ack's sender (`ackWhy`)
    icases Hwhy with %h
    exfalso; apply h; rw [hld]; exact swift.rid_leader bw' c.N b hN Hbw'.1 Hbw'.2
  · rw [decide_eq_false hld]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iunfold swift.ackP
    iexists l, fa
    iframe Hl HDep
    ipureintro; exact ⟨rfl, Hx, rfl⟩))

set_option hygiene false in
/-- `desc.fastPathH.Add(msg.Replica, msg.Replica == r.leader(), msg)` and the end of
`commonCaseFastAck` (the names of its proof; the slow set's data `HdS`, its lent state `HR`). -/
macro "fastAdd" : tactic => `(tactic| (
  ihave ⟨HR, HdF⟩ := swift.setR_swap $$ [HR HdS]
  · iframe HR HdS
  ihave ⟨%qe', %bw', Hbal, HsF, HfF, %Hbw', HRb⟩ := swift.setR_open $$ HR
  wp_apply (swift.Replica.wp_leader wp_Leader c.rp c.rr bw' _ c.N hN) $$ [Hbal] as Hbal
  · iframe Hbal Hrr HN
  try wp_auto
  ihave HR := HRb $$ Hbal HsF HfF
  ihave #HhFq := swift.descOwn_hdF c RC MP γd d x b Do iprop(Do ∗ swift.ocfRes d cf cond fs v) s f qS qF
    szS szF memS memF hd (swift.ocfDc_ok d cf cond fs v Do) $$ [HhS HhF]
  · iframe HhS HhF
  wp_apply (wp_Add f qF szF memF (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True)
      (swift.setR c RC MP γd d x b iprop(Do ∗ swift.ocfRes d cf cond fs v) s f qS szS memS hd false)
      (swift.descGone c b x d) hd
      fa.Replica' (decide (fa.Replica' = BitVec.srem bw' (W32 (sint.Z (W64 (c.N : Int))))))
      (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l)) $$ [HdF HR]
    as %added ⟨-, Hres⟩
  · iframe HdF HR HhFq
    isplitr
    · imodintro; iintro HR; isplitl []; · itrivial
      iintro -; iexact HR
    ackCond
  iapply HΦ
  icases Hres with (⟨HdF, HR⟩ | Hex)
  · ileft
    ihave ⟨HR, HdS⟩ := swift.setR_swap' $$ [HR HdF]
    · iframe HR HdF
    ihave ⟨HR, Hocf⟩ := swift.setR_take $$ HR
    iframe Hocf
    iunfold swift.descOwn
    iexists s, f, qS, qF, szS, szF, memS, memF, hd
    iframe HhS HhF HdS HR
  · iright; iunfold swift.descDone; iexact Hex))

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- The ballot's read share and the sets' fields out of the handler's lent state, and back. -/
theorem swift.setR_open (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) (s f : Loc) (qO : GoInterface) (szO : Nat) (memO : w32 → Prop)
    (hd : GoFunc) (slow : Bool) :
    swift.setR c RC MP γd d x b Do s f qO szO memO hd slow ⊢
      ∃ (qe : Qp) (bw : w32), typedPointsto (swift.fld c.rp go!"ballot") bw (DFrac.own qe) ∗
        swift.dfld d go!"slowPathH" ↦ s ∗ swift.dfld d go!"fastPathH" ↦ f ∗
        ⌜sp.bal bw = b ∧ 0 ≤ sint.Z bw⌝ ∗
        (typedPointsto (swift.fld c.rp go!"ballot") bw (DFrac.own qe) -∗
          swift.dfld d go!"slowPathH" ↦ s -∗ swift.dfld d go!"fastPathH" ↦ f -∗
          swift.setR c RC MP γd d x b Do s f qO szO memO hd slow) := by
  unfold swift.setR swift.descSt swift.epochRd
  iintro ⟨%qe, %bw, %stp, %rcp, %dv, %rv, ⟨Hbal, HStf, Hrcf, Het, Hxe, %Hbw⟩, Hsh, HRC, Hd, Htok, Hcom,
    #Hra, %Hph, #Hpw, #Hdw, %Hrp, #HsB, ⟨HsF, HfF, HRs⟩⟩
  iexists qe, bw
  iframe Hbal HsF HfF
  isplitr
  · ipureintro; exact Hbw
  iintro Hbal HsF HfF
  iexists qe, bw, stp, rcp, dv, rv
  iframe Hsh Hbal HStf Hrcf Het Hxe HRC Hd Htok Hcom Hra HRs HsF HfF Hpw Hdw HsB
  isplitr
  · ipureintro; exact Hbw
  isplitr
  · ipureintro; exact Hph
  ipureintro; exact Hrp

/-- The slow set's lent state with the slow set's data is the fast set's with the fast set's
data. -/
theorem swift.setR_swap (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) (s f : Loc) (qS qF : GoInterface) (szS szF : Nat)
    (memS memF : w32 → Prop) (hd : GoFunc) :
    swift.setR c RC MP γd d x b Do s f qF szF memF hd true ∗
      replica.mset.ownD s qS szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True) hd ⊢
    swift.setR c RC MP γd d x b Do s f qS szS memS hd false ∗
      replica.mset.ownD f qF szF memF (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True) hd := by
  unfold swift.setR swift.descSt
  iintro ⟨⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, #Hra, %Hph, #Hpw, #Hdw, %Hrp, #HsB,
    ⟨HsF, HfF, HdF, HDo⟩⟩, HdS⟩
  simp only [↓reduceIte, Bool.false_eq_true]
  iframe HdF
  iexists qe, bw, stp, rcp, dv, rv
  iframe Hsh Hrd HRC Hd Htok Hcom Hra HsF HfF HdS HDo Hpw Hdw HsB
  isplitr
  · ipureintro; exact Hph
  ipureintro; exact Hrp

/-- `setR_swap` back. -/
theorem swift.setR_swap' (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) (s f : Loc) (qS qF : GoInterface) (szS szF : Nat)
    (memS memF : w32 → Prop) (hd : GoFunc) :
    swift.setR c RC MP γd d x b Do s f qS szS memS hd false ∗
      replica.mset.ownD f qF szF memF (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True) hd ⊢
    swift.setR c RC MP γd d x b Do s f qF szF memF hd true ∗
      replica.mset.ownD s qS szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x) iprop(True) hd := by
  unfold swift.setR swift.descSt
  iintro ⟨⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, #Hra, %Hph, #Hpw, #Hdw, %Hrp, #HsB,
    ⟨HsF, HfF, HdS, HDo⟩⟩, HdF⟩
  simp only [↓reduceIte, Bool.false_eq_true]
  iframe HdS
  iexists qe, bw, stp, rcp, dv, rv
  iframe Hsh Hrd HRC Hd Htok Hcom Hra HsF HfF HdF HDo Hpw Hdw HsB
  isplitr
  · ipureintro; exact Hph
  ipureintro; exact Hrp

/-- The ballot's read share out of the owner state, and back. -/
theorem swift.descOwn_ballot (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) :
    swift.descOwn c RC MP γd d x b Do ⊢
      ∃ (qe : Qp) (bw : w32), typedPointsto (swift.fld c.rp go!"ballot") bw (DFrac.own qe) ∗
        ⌜sp.bal bw = b ∧ 0 ≤ sint.Z bw⌝ ∗
        (typedPointsto (swift.fld c.rp go!"ballot") bw (DFrac.own qe) -∗
          swift.descOwn c RC MP γd d x b Do) := by
  unfold swift.descOwn
  iintro ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF, HdS, HR⟩
  ihave ⟨%qe, %bw, Hbal, HsF, HfF, %Hbw, HRb⟩ := swift.setR_open $$ HR
  iexists qe, bw
  iframe Hbal
  isplitr
  · ipureintro; exact Hbw
  iintro Hbal
  ihave HR := HRb $$ Hbal HsF HfF
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe HhS HhF HdS HR

/-- `setR_open` with the owner's reader bundle out too (round 25, SW4), and its pin at the epoch
share's `q` (round 43, table §3R11b). -/
theorem swift.setR_openR (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) (s f : Loc) (qO : GoInterface) (szO : Nat) (memO : w32 → Prop)
    (hd : GoFunc) (slow : Bool) :
    swift.setR c RC MP γd d x b Do s f qO szO memO hd slow ⊢
      ∃ (qe : Qp) (bw : w32), typedPointsto (swift.fld c.rp go!"ballot") bw (DFrac.own qe) ∗
        swift.dfld d go!"slowPathH" ↦ s ∗ swift.dfld d go!"fastPathH" ↦ f ∗
        ⌜sp.bal bw = b ∧ 0 ≤ sint.Z bw⌝ ∗ swift.ownRdr c.rp c.γdl ∗ swift.epochPinQ c.γxp qe b ∗
        (typedPointsto (swift.fld c.rp go!"ballot") bw (DFrac.own qe) -∗
          swift.dfld d go!"slowPathH" ↦ s -∗ swift.dfld d go!"fastPathH" ↦ f -∗
          swift.ownRdr c.rp c.γdl -∗ swift.epochPinQ c.γxp qe b -∗
          swift.setR c RC MP γd d x b Do s f qO szO memO hd slow) := by
  unfold swift.setR swift.descSt swift.epochRd
  iintro ⟨%qe, %bw, %stp, %rcp, %dv, %rv, ⟨Hbal, HStf, Hrcf, Het, Hxe, %Hbw⟩, Hsh, HRC, Hd, Htok, Hcom,
    #Hra, %Hph, #Hpw, #Hdw, %Hrp, #HsB, ⟨HsF, HfF, HRs⟩⟩
  iunfold swift.shOwn at Hsh
  icases Hsh with ⟨Hshe, HshR⟩
  ihave ⟨HrdR, Hpin, Hshr⟩ := swift.shOwnR_rdrP c d b qe $$ HshR
  iexists qe, bw
  iframe Hbal HsF HfF HrdR Hpin
  isplitr
  · ipureintro; exact Hbw
  iintro Hbal HsF HfF HrdR Hpin
  ihave HshR := Hshr $$ HrdR Hpin
  ihave Hsh : swift.shOwn c d b qe $$ [Hshe HshR]
  · iunfold swift.shOwn; iframe Hshe HshR
  iexists qe, bw, stp, rcp, dv, rv
  iframe Hsh Hbal HStf Hrcf Het Hxe HRC Hd Htok Hcom Hra HRs HsF HfF Hpw Hdw HsB
  isplitr
  · ipureintro; exact Hbw
  isplitr
  · ipureintro; exact Hph
  ipureintro; exact Hrp

/-- `descOwn_ballot` with the owner's reader bundle out too (round 25, SW4), and its pin at the
epoch share's `q` (round 43, table §3R11b). -/
theorem swift.descOwn_ballotR (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do : IProp netDistGF) :
    swift.descOwn c RC MP γd d x b Do ⊢
      ∃ (qe : Qp) (bw : w32), typedPointsto (swift.fld c.rp go!"ballot") bw (DFrac.own qe) ∗
        ⌜sp.bal bw = b ∧ 0 ≤ sint.Z bw⌝ ∗ swift.ownRdr c.rp c.γdl ∗ swift.epochPinQ c.γxp qe b ∗
        (typedPointsto (swift.fld c.rp go!"ballot") bw (DFrac.own qe) -∗
          swift.ownRdr c.rp c.γdl -∗ swift.epochPinQ c.γxp qe b -∗
          swift.descOwn c RC MP γd d x b Do) := by
  unfold swift.descOwn
  iintro ⟨%s, %f, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF, HdS, HR⟩
  ihave ⟨%qe, %bw, Hbal, HsF, HfF, %Hbw, HrdR, Hpin, HRb⟩ := swift.setR_openR $$ HR
  iexists qe, bw
  iframe Hbal HrdR Hpin
  isplitr
  · ipureintro; exact Hbw
  iintro Hbal HrdR Hpin
  ihave HR := HRb $$ Hbal HsF HfF HrdR Hpin
  iexists s, f, qS, qF, szS, szF, memS, memF, hd
  iframe HhS HhF HdS HR

/-- A part `B` of the handler's lent frame out (the owner frame `Do ∗ B`). -/
theorem swift.setR_take (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do B : IProp netDistGF) (s f : Loc) (qO : GoInterface) (szO : Nat) (memO : w32 → Prop)
    (hd : GoFunc) (slow : Bool) :
    swift.setR c RC MP γd d x b iprop(Do ∗ B) s f qO szO memO hd slow ⊢
      swift.setR c RC MP γd d x b Do s f qO szO memO hd slow ∗ B := by
  unfold swift.setR swift.descSt
  iintro ⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, #Hra, %Hph, #Hpw, #Hdw,
    %Hrp, #HsB, ⟨HsF, HfF, HdO, HDo, HB⟩⟩
  iframe HB
  iexists qe, bw, stp, rcp, dv, rv
  iframe Hsh Hrd HRC Hd Htok Hcom Hra HsF HfF HdO HDo Hpw Hdw HsB
  isplitr
  · ipureintro; exact Hph
  ipureintro; exact Hrp

/-- `setR_take` back. -/
theorem swift.setR_give (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (Do B : IProp netDistGF) (s f : Loc) (qO : GoInterface) (szO : Nat) (memO : w32 → Prop)
    (hd : GoFunc) (slow : Bool) :
    swift.setR c RC MP γd d x b Do s f qO szO memO hd slow ∗ B ⊢
      swift.setR c RC MP γd d x b iprop(Do ∗ B) s f qO szO memO hd slow := by
  unfold swift.setR swift.descSt
  iintro ⟨⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, Hcom, #Hra, %Hph, #Hpw, #Hdw,
    %Hrp, #HsB, ⟨HsF, HfF, HdO, HDo⟩⟩, HB⟩
  iexists qe, bw, stp, rcp, dv, rv
  iframe Hsh Hrd HRC Hd Htok Hcom Hra HsF HfF HdO HDo HB Hpw Hdw HsB
  isplitr
  · ipureintro; exact Hph
  ipureintro; exact Hrp

end lemmas

section hdLemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [hook.Assumptions]

/-- **The slow set's handler spec at the frame `Dc`** (round 33, G-cap): from `descOwn`'s
`acksHdOk` and `slotCap` (over `F`), when `Dc` holds an `OptCondF` part and `F`. -/
theorem swift.descOwn_hdS (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (F Dc : IProp netDistGF) (s f : Loc) (qS qF : GoInterface) (szS szF : Nat)
    (memS memF : w32 → Prop) (hd : GoFunc)
    (h : Dc ⊢ ∃ (cf : Loc) (cond : GoFunc) (fs : List GoFunc) (v : Bool),
      swift.ocfRes d cf cond fs v ∗ F) :
    swift.acksHdOk c RC MP γd d x b hd ∗ swift.slotCap c MP γd d x b F ⊢
      □ replica.mset.handlerOkQ s qS hd szS memS (swift.ackP x) swift.ackA (swift.leadAckP c b x)
        iprop(True) (swift.setR c RC MP γd d x b Dc s f qF szF memF hd true)
        (swift.descGone c b x d) := by
  iintro ⟨#Hhd, #Hcap⟩
  iunfold swift.acksHdOk at Hhd
  unfold swift.setR
  imodintro
  iapply Hhd
  iapply (swift.slotCap_R c MP γd d x b F s _ ?_) $$ Hcap
  iintro ⟨⟨Hs, Hf, HdO, HDc⟩, Hms⟩
  ihave ⟨%cf, %cond, %fs, %v, Hocf, HF⟩ := h $$ HDc
  iexists s, f, cf, cond, fs, v
  iframe Hs Hf Hms Hocf HF
  simp only [↓reduceIte]
  iapply swift.msetF_of $$ HdO

/-- The fast set's (see `descOwn_hdS`). -/
theorem swift.descOwn_hdF (c : swift.DC) (RC : Loc → w32 → IProp netDistGF)
    (MP : GoInterface → IProp netDistGF) (γd : ChanNames) (d : Loc) (x : swift.CommandId) (b : Nat)
    (F Dc : IProp netDistGF) (s f : Loc) (qS qF : GoInterface) (szS szF : Nat)
    (memS memF : w32 → Prop) (hd : GoFunc)
    (h : Dc ⊢ ∃ (cf : Loc) (cond : GoFunc) (fs : List GoFunc) (v : Bool),
      swift.ocfRes d cf cond fs v ∗ F) :
    swift.acksHdOk c RC MP γd d x b hd ∗ swift.slotCap c MP γd d x b F ⊢
      □ replica.mset.handlerOkQ f qF hd szF memF (swift.ackP x) swift.ackA (swift.leadAckP c b x)
        iprop(True) (swift.setR c RC MP γd d x b Dc s f qS szS memS hd false)
        (swift.descGone c b x d) := by
  iintro ⟨#Hhd, #Hcap⟩
  iunfold swift.acksHdOk at Hhd
  unfold swift.setR
  imodintro
  iapply Hhd
  iapply (swift.slotCap_R c MP γd d x b F f _ ?_) $$ Hcap
  iintro ⟨⟨Hs, Hf, HdO, HDc⟩, Hms⟩
  ihave ⟨%cf, %cond, %fs, %v, Hocf, HF⟩ := h $$ HDc
  iexists s, f, cf, cond, fs, v
  iframe Hs Hf Hms Hocf HF
  simp only [Bool.false_eq_true, ↓reduceIte]
  iapply swift.msetF_of $$ HdO

/-- The frame `Do ∗ ocfRes` has an `OptCondF` part and `Do`. -/
theorem swift.ocfDc_ok (d cf : Loc) (cond : GoFunc) (fs : List GoFunc) (v : Bool) (Do : IProp netDistGF) :
    iprop(Do ∗ swift.ocfRes d cf cond fs v) ⊢ ∃ (cf' : Loc) (cond' : GoFunc) (fs' : List GoFunc) (v' : Bool),
      swift.ocfRes d cf' cond' fs' v' ∗ Do := by
  iintro ⟨HDo, Hocf⟩
  iexists cf, cond, fs, v
  iframe

end hdLemmas

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [sync.Assumptions] [hook.Assumptions]
  [github_com.orcaman.concurrent_map.Assumptions]

end proof

section proofOcf
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [sync.Assumptions] [hook.Assumptions]
  [github_com.orcaman.concurrent_map.Assumptions]

end proofOcf

end Perennial.github_com.imdea_software.swiftpaxos
