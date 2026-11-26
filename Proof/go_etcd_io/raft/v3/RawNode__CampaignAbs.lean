/-
Antithesis parity B1, phase 2 (#33, `notes/antithesis-parity-design.md` §4). **`RawNode.Campaign`, the
strengthened triple** (`RawNode.Campaign.absSpec`, `RawNodeAbsSpecs.lean`). The proof is
`RawNode__Campaign.lean`'s, over `ownRawNodeAt`: the message `pb.Message{Type: MsgHup}` built as before,
then `raft.Step`
- in the scope, at the no-snapshot flag (`raft.Step.untracedNs`, `RaftStepNoSnap.lean`), whose post gives
  `StepEnd`, read through `toRState` as `CampaignEndR` (`campaignEndR_of_stepEnd_hup`, `StepEndIp.lean`:
  `hup`'s guard, the log facts `hasUnappliedConfChanges` reads, the ghost prefix empty at the boundary
  `0`); the log's state kept (`logst_of_stepEnd_hup`), so the in-progress boundary too; the scope kept
  as a tick's (`TickEnd` of the same `StepEnd`: votes queued only);
- outside it, untraced as before (`raft.Step.untraced`).
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Campaign
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasRawnodeR
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Proof.go_etcd_io.raft.v3.TracedUntracedRaftStep
public import Proof.go_etcd_io.raft.v3.RaftStepNoSnap
public import Proof.go_etcd_io.raft.v3.RawNodeAtScope
public import Proof.go_etcd_io.raft.v3.StepEndIp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A premise of `Step` about another message type: `MsgHup` (`W32 0`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

set_option hygiene false in
/-- `raft.Step`'s message, credit and transfer clause (the frame of both instances, up to the snapshot
clause). -/
local macro "hup_frame" : tactic => `(tactic| (
    simp only [hP, ↓reduceIte, named]
    isplitr
    · imodintro
      iintro %h
      exact absurd h.1 (by msg_ne)
    isplitl [Hm]
    · isplitl [Hm]
      · iapply msgIn_toC (by decide) _ _ _ $$ Hm
      repeat (isplitr; · first | iempintro | (ipureintro; simp) | (ipureintro; msg_ne))
      imodintro
      iintro %ty %Hty
      rw [show mtypeOf (W32 0) = none from rfl] at Hty
      cases Hty
    isplitl [Hcr]
    · rw [ite_eq_right (by msg_ne)]; iexact Hcr))

set_option hygiene false in
/-- After `raft.Step` (either instance; in the scope `Hx`: the step's end state, the ghost prefix empty):
`ownRawNodeAt` at the end state, the exact effect in the scope. -/
local macro "hup_tail" : tactic => `(tactic| (
    have Hc := Href.commit_mono
    have e1 := Href.keep (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne)); subst e1
    have e2 := Hcc (by msg_ne); subst c'
    wp_auto
    obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩ :=
      Hfr (by msg_ne) (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne))
    icases ownRaftPhysC_sn cf rnv.raft' id s' $$ Hphys with ⟨%Hsn1, Hphys⟩
    icases ownRaftPhysC_inprogress_pos cf rnv.raft' id s' $$ Hphys with ⟨%Hip1, Hphys⟩
    icases ownRaftPhysC_cq cf rnv.raft' id s' $$ Hphys with ⟨#Hcq1, Hphys⟩
    icombine Hcq0 Hcq1 gives %Hcqe
    have Hcq' : s'.cq = s.cq := by first | exact Hcqe.symm | exact Hcqe
    icases ownRaftPhysC_sdr cf rnv.raft' id s' $$ Hphys with ⟨#Hsd1, Hphys⟩
    icombine Hsd0 Hsd1 gives %Hsde
    have Hsdr' : s'.sdr = s.sdr := by first | exact Hsde.symm | exact Hsde
    obtain ⟨Ht1, Ht2, -, Hip4, -, Hpcs⟩ := Htm (by msg_ne)
    have Ht2' := Ht2 rfl
    ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Hip4 (by msg_ne)) $$ Hstrecs
    -- in the scope, the campaign read as a tick's `TickEnd` (for the scope), the log's state kept
    have Hlifted : sc = true → TickEnd rs.k cf id (toPState s) (toPState s') ∧ s'.logst = s.logst :=
      fun h => ⟨tickEnd_of_stepEnd_hup (Hlift h).1 rfl rfl (Hx h).1,
        logst_of_stepEnd_hup rfl rfl (Hx h).1⟩
    ihave Hsc := rnScopeAt_keepIf sc rs { rs with term := s'.term } s s'
      (fun h Hs => by
        have hro := tickEnd_rd_out (Hlifted h).1
        exact RnScopeBasic.keep Hs rfl rfl Hpre Hcq' hro.1 Hpv Hsn hro.2
          (tickEnd_ro (Hlifted h).1)) Hsg (fun _ => Hsdr') $$ Hsc
    ihave Hrntr := rnTrace_none (GF := GF) γ rnv.raft' id cf rs.delivered s'
      (by rw [Hgh]; exact Hgtr.trans HtrG)
    icases Herr with (%Herr | ⟨%Hc', -⟩)
    · iapply HΦ $$ %err %s'.term %(toRState { rs with term := s'.term } fp s') %(uint.nat s'.logst.inprogress - 1)
      simp only [named]
      isplitl [Hrn Hphys Hghost Hsteps Hsteps_cap Hpend Hledger Hrntr Hsc]
      ihave #Hhist' := restoredSnapHistory_keep γ id Hsd $$ Hhist
      ihave Hledger' := restoreLedger_keep γ id rs.sn (s := s) (s' := s')
        (by first | exact Href.voteLe.1 | exact Hcv.1.voteLe.1 | exact Hvr.1 | omega)
        (logStoreRec_ksn Hsd) (by first | exact Href.commit_mono | exact Hcv.commit | exact Hc) (by first | exact Href.snapQueue | exact Hcv.queue | exact Hcv.1.snapQueue) $$ Hledger
      ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
      · iapply ownRawNodeAt_intro γ rn id { rs with term := s'.term } (toRState { rs with term := s'.term } fp s') qs
          (uint.nat s'.logst.inprogress - 1) (basicScope sc) s' cf fp rnv sv hprev steps Hwf' Hin
          Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
          (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, (logStoreRec_stored Hsd)⟩ Hc Ha (tc_le_of_gh Hgh) Hstok) rfl
          (by rw [Hsg]; exact ⟨Hstor.1, by rw [Hsn1.2, Hgh, ← Hns0.2]; exact Hstor.2⟩)
          (Hpvoff.step rfl rfl Hpre Hgh (by omega) Hpcs (fun _ => Htc1))
          (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
          (RNFl.keep Hrnfl Hfl' Hap' Ha) (Hloan.keep Hgh Hsn Hfl' (logStoreRec_stored Hsd) Hu Ha Hc)
          (Hsdt.ofRec Hsn Hsd) Hrole
          (Hphs.keep rfl rfl rfl (HsLe.of_step Href.voteLe Hc) Hsn (.inl (Hip4 (by msg_ne)))) rfl (by omega)
          (by rw [Hgh]; exact Hgtr) (by rw [Hgh]; exact Hglq)
          $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' Hhist' Hledger' [Hdur] Hrntr Hsc
        · iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hsn Hpv (logStoreRec_stored Hsd) $$ Hdur
      ipureintro
      refine ⟨by rw [Htrm]; exact ⟨Ht1, Ht2'⟩, Herr, ?_⟩
      intro md hmd
      have h : sc = true := by cases sc <;> first | rfl | cases hmd
      have hl := (Hlifted h).2
      have hlog : (toPState s').log = ps.p.log := by
        rw [← Hps]
        show s'.logst.sents ++ s'.logst.uents = s.logst.sents ++ s.logst.uents
        rw [hl]
      refine ⟨?_, ?_⟩
      · rw [← Hps]
        obtain ⟨Hend1, Hfp0, -⟩ := Hx h
        subst Hfp0
        exact campaignEndR_of_stepEnd_hup (Hlift h).1 (by rw [← Hkt h]; exact (Hlift h).1.1)
          (Hcfm.2 (Hcin h).2.2.2.1) rfl rfl (Hp0 h) Hlogf.2.1 Hlogf.2.2 Hend1 ⟨rfl, rfl⟩
      · show uint.nat s'.logst.inprogress - 1 = min ip (lcpLen ps.p.log (toPState s').log)
        rw [hl, Hip, Nat.add_sub_cancel]
        exact ip_eq_min_of_eq (Hipl h) hlog
    · exfalso; revert Hc'; msg_ne))

/-- **`RawNode.Campaign`, strengthened** (`RawNode.Campaign.absSpec`). -/
theorem RawNode.Campaign.wp_absProof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    RawNode.Campaign.absSpec (GF := GF) (hG := hG) := by
  have wp_raft_StepNs := raft.Step.untracedNs wp_raft_Step
  have wp_raft_Step := raft.Step.untraced wp_raft_Step
  intro sc γ rn id rs ps qs ip Hterm Hflw HtrG
  wp_start as H
  iNamed H
  iNamed Hrn
  -- the scope's facts at the start state
  icases rnScopeAt_scope sc rs s $$ Hsc with ⟨%Hscope, Hsc⟩
  icases rnScopeAt_ktie sc rs s $$ Hsc with ⟨%Hkt, Hsc⟩
  icases ownRaftPhysC_precand cf rnv.raft' id s $$ Hphys with ⟨%Hpre0, Hphys⟩
  icases ownRaftPhysC_ipFacts cf rnv.raft' id s $$ Hphys with ⟨%Hipf, Hphys⟩
  icases ownRaftPhysC_trkDoms cf rnv.raft' id s $$ Hphys with ⟨%Hdom, Hphys⟩
  icases ownRaftPhysC_ackScope cf rnv.raft' id s $$ Hphys with ⟨%Hal0, Hphys⟩
  icases ownRaftPhysC_cq cf rnv.raft' id s $$ Hphys with ⟨#Hcq0, Hphys⟩
  icases ownRaftPhysC_sdr cf rnv.raft' id s $$ Hphys with ⟨#Hsd0, Hphys⟩
  icases ownStepGhost_followerVotes γ _ cf id s $$ Hghost with ⟨%Hfv, Hghost⟩
  icases rnScopeAt_cfgIn sc rs s $$ Hsc with ⟨%Hcin, Hsc⟩
  icases ownStepGhost_cfgScope γ rs fp _ cf id s $$ Hghost with ⟨%Hcfm, Hghost⟩
  have Hlift : sc = true → LiftScope cf id s ∧ AckScope cf := fun h => by
    have Hs := Hscope h
    obtain ⟨HC, Hid⟩ := cfgScope_of Hs (Hcin h) Hcfm
    have Hv : cf.voters = γ.reCfg := HC.voters
    exact ⟨liftScope_of Hs Hpre0 Hfv Hdom.1 Hdom.2 (by rw [Hv]; exact Hid), Hal0 HC.2.1⟩
  have Hp0 : sc = true → uint.Z s.logst.prev.index' = 0 := fun h => by
    rw [(Hscope h).2.2.2.2.2.1]; rfl
  have Hipl : sc = true → ip ≤ ps.p.log.length := fun h => by
    rw [← Hps]
    exact ip_le_log Hip (by rw [(Hscope h).2.2.2.2.2.1]; rfl) Hipf.1.2
  -- the log facts `hasUnappliedConfChanges` reads (as `raft__Step/MsgHup.lean`)
  icases ownRaftPhysC_log_same cf rnv.raft' id s $$ Hphys with ⟨Hlog, Hback⟩
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hcm, Hlog⟩
  icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hlnw, Hlog⟩
  ihave Hphys := Hback $$ Hlog
  have Hlogf : (s.logst.snap = none → uint.Z s.logst.prev.index' ≤ uint.Z s.logst.applied) ∧
      uint.Z s.logst.applied ≤ uint.Z s.logst.committed ∧ uint.Z s.logst.committed + 1 < 2 ^ 64 :=
    ⟨Hcm.2, Hcm.1.2.1, by have := Hcm.1.2.2; omega⟩
  have Htc1 : uint.Z s.term + 1 ≤ uint.Z s.gh.tc := by rw [← Htrm, ← Hpvoff.2.1]; exact Hterm
  have Hnw : uint.Z s.term + 1 < 2 ^ 64 := by have : uint.Z s.gh.tc < 2 ^ 64 := by word
                                              omega
  wp_auto_lc 1
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 0) as %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  imod msgOwn_lit0 «$a0_ptr» _ ({ (zero_val MessageM) with Type' := W32 0 } : MessageM) ⊤ $$ [«$a0»] with Hm
  · iframe «$a0» cTy
    isplitr
    · ipureintro; simp
    msg_nulls
  ihave Hm := msgOwn_to_msgIn _ _ (by simp [MsgApp]) $$ Hm
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
  icases ownRaftPhysC_sn cf rnv.raft' id s $$ Hphys with ⟨%Hns0, Hphys⟩
  have hP : (W32 0 : w32) ≠ MsgProp := by simp [MsgProp]
  by_cases hsc : sc = true
  · icases rnScopeAt_cap hsc rs s $$ Hsc with ⟨#Hcap, Hsc⟩
    icases ownStepGhost_fp_nil γ rs fp ds cf id s (Hcin hsc).2.2.2.1 (Hscope hsc).2.2.2.2.2.1 $$ Hghost
      with ⟨%Hfp0, Hghost⟩
    wp_apply wp_raft_StepNs cf _ γ _ id s «$a0_ptr» ({ (zero_val MessageM) with Type' := W32 0 } : MessageM)
      [] [] none []
      (by simp [StepMsg, stepMsgTypes, MsgHup])
      (fun _ => ⟨rfl, Hnw, fun _ => Htc1, Hrnfl.1 Hflw⟩)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne)
      (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
      (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
      (by tr_none) (Hlift hsc).2 $$ [$Hphys $Hghost $Hlc1 Hcr Hm]
    · hup_frame
      isplitr
      · imodintro
        iintro %Hc
        simp [MsgSnap] at Hc
      isplitr
      · iexact Hcap
      isplitr
      · ipureintro; exact Hp0 hsc
      · ipureintro; exact (Hscope hsc).2.2.2.2.2.2.2.1
    simp only [hP]
    iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, -, %Htm, -, -, -, Herr,
      %Hend, -, %Hns', -⟩
    have Hx : sc = true → StepEnd cf id ({ (zero_val MessageM) with Type' := W32 0 } : MessageM)
        [] [] s s' ∧ fp = [] ∧ NoSnapL s'.outbox := fun _ => ⟨Hend, Hfp0, Hns'⟩
    hup_tail
  · wp_apply wp_raft_Step cf _ γ _ id s «$a0_ptr» ({ (zero_val MessageM) with Type' := W32 0 } : MessageM)
      [] [] none []
      (by simp [StepMsg, stepMsgTypes, MsgHup])
      (fun _ => ⟨rfl, Hnw, fun _ => Htc1, Hrnfl.1 Hflw⟩)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne)
      (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
      (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
      (by tr_none) $$ [$Hphys $Hghost $Hlc1 Hcr Hm]
    · hup_frame
      imodintro
      iintro %Hc
      simp [MsgSnap] at Hc
    simp only [hP]
    iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, -, %Htm, -, -, -, Herr⟩
    have Hx : sc = true → StepEnd cf id ({ (zero_val MessageM) with Type' := W32 0 } : MessageM)
        [] [] s s' ∧ fp = [] ∧ NoSnapL s'.outbox := fun h => absurd h hsc
    hup_tail

end proof

end EtcdGrove
end Perennial
