/-
#33 S4 (P-raft-3), `notes/antithesis-rawnode-design.md` §2.2, §2.7. **`RawNode.Propose`, the
strengthened triple** (`RawNode.Propose.absSpec`, `RawNodeAbsSpecs.lean`); the old spec is its
corollary (`RawNode.Propose.spec_of_abs`, `RawNodeSpecOfAbs.lean`). The proof is
`RawNode__Propose.lean`'s, over `ownRawNodeAt`: the message built as before, then `raft.Step`
- in the scope, at the no-snapshot flag (`raft.Step.untracedNs`, `RaftStepNoSnap.lean`: the storage
  never compacted, the log's boundary at `0`, no `MsgSnap` queued, no automatic leave at the static
  node's non-joint configuration, `ownRaftPhysC_ackScope`), whose post gives `StepEnd`, read through
  `toPState` as `ProposeEnd` (`proposeEnd_of_stepEnd`, `InputEndLift.lean`), and the log only appended
  to with the in-progress boundary kept (`logGrow_of_stepEnd_prop`, `StepEndIp.lean`); the scope kept
  (`RnScope.keep`: the read-index state, `proposeEnd_rd`; no `MsgSnap` queued);
- outside it, untraced as before (`raft.Step.untraced`).

A sibling of the function's proof file, which `RawNode__Propose.lean` applies.
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Propose
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasRawnodeR
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage
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

/-- A premise of `Step` about another message type: `MsgProp` (`W32 2`) is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

set_option hygiene false in
/-- `raft.Step`'s message, entry tokens, credit and snapshot clause (the frame of both instances). -/
local macro "prop_frame" : tactic => `(tactic| (
    simp only [MsgProp, ite_true]
    isplitr
    · imodintro
      iintro %h
      exact absurd h.1 (by msg_ne)
    isplitl [Hm Htk]
    · simp only [named]
      isplitl [Hm]
      · rw [flag_moves (by decide : movesB (W32 2) = true)]; iexact Hm
      isplitl [Htk]
      · isplitr
        · iexists ([propEntryM data].map fun _ => none)
          iapply ccEntsOk_normal [propEntryM data]
          intro e He
          simp only [List.mem_singleton] at He
          subst He
          rfl
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => entTk (GF := GF) γ e)).2
        iexact Htk
      isplitr
      · ipureintro
        intro _
        exact ⟨List.cons_ne_nil _ _, by simp⟩
      isplitr
      · ipureintro; simp
      isplitr
      · ipureintro
        intro Hc
        simp [MsgStorageApplyResp] at Hc
      · imodintro
        iintro %ty %Hty _
        rw [show mtypeOf (W32 2) = some .propose from rfl] at Hty
        cases Hty
        unfold isMessage absMsg absMsgFrom
        isplitr
        · ipureintro
          exact ⟨rfl, List.cons_ne_nil _ _, by simp, fun e _ => TrNoConf.of_none HtrG e⟩
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => propData (GF := GF) γ e)).2
        iexact Hent
    isplitl [Hcr]
    · rw [ite_eq_right (by msg_ne)]; iexact Hcr))

set_option hygiene false in
/-- After `raft.Step` (either instance, the end state in the scope as `Hx`): `ownRawNodeAt` at the
end state, the exact effect in the scope. -/
local macro "prop_tail" : tactic => `(tactic| (
    have Hc := Href.commit_mono
    have e1 := Href.keep (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne)); subst e1
    have e2 := Hc' (by msg_ne); subst c'
    wp_auto
    obtain ⟨Hfr, Hap, -⟩ := Hloc.1 (fun h => absurd h (by msg_ne)) (.inl rfl)
    icases ownRaftPhysC_sn cf rnv.raft' id s' $$ Hphys with ⟨%Hsn1, Hphys⟩
    icases ownRaftPhysC_inprogress_pos cf rnv.raft' id s' $$ Hphys with ⟨%Hip1, Hphys⟩
    icases ownRaftPhysC_cq cf rnv.raft' id s' $$ Hphys with ⟨#Hcq1, Hphys⟩
    icombine Hcq0 Hcq1 gives %Hcqe
    have Hcq' : s'.cq = s.cq := by first | exact Hcqe.symm | exact Hcqe
    have Hap' := Hap (fun Hc => absurd Hc (by msg_ne))
    ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok (by rw [Hfr.1]; exact Int.le_refl _)
      Hfr.2.2.2.2.1 Hfr.2.2.2.1 (logStoreRec_stored Hfr.2.2.2.2.2.1) Hfr.2.1 $$ Hstrecs
    -- in the scope, the proposal's exact effect, the log only appended to
    have Hlifted : sc = true →
        ProposeEnd cf id (toPState s)
          (absMsg .propose ({ (zero_val MessageM) with Type' := W32 2, From' := id } : MessageM)
            [propEntryM data] []) (toPState s') ∧ LogGrow s.logst s'.logst := fun h =>
      ⟨proposeEnd_of_stepEnd (Hlift h).1 rfl rfl (noSnapSent_of_noSnapL (Hx h).2) (Hx h).1,
        logGrow_of_stepEnd_prop (Hlift h).1 rfl rfl (Hx h).1⟩
    ihave Hsc := rnScopeAt_keepIf sc rs rs s s'
      (fun h Hs => by
        have hrd : s'.rd.pend = s.rd.pend := by
          rw [← toPState_rd_pend s', ← toPState_rd_pend s, proposeEnd_rd (Hlifted h).1]
        exact RnScope.keep Hs rfl rfl Hfr.2.2.2.2.2.2.2.1 Hcq' hrd Hfr.2.2.2.2.1 Hfr.2.2.2.1
          (fun m hm => .inr ((Hx h).2 m hm))
          (fun h0 => by rw [proposeEnd_rd (Hlifted h).1]; exact h0)
          (hxs := congrArg NGhost.xs Hfr.2.2.2.2.2.2.2.2.1)) Hfr.2.2.2.2.2.2.1 $$ Hsc
    ihave Hrntr := rnTrace_none (GF := GF) γ rnv.raft' id cf rs.delivered s'
      (by rw [LocalFrame.ns Hfr]; exact Hgtr.trans HtrG)
    iapply HΦ $$ %err %(toPState s') %(uint.nat s'.logst.inprogress - 1)
    simp only [named]
    isplitl [Hrn Hphys Hghost Hsteps Hsteps_cap Hpend Hledger Hrntr Hsc]
    ihave #Hhist' := restoredSnapHistory_keep γ id Hfr.2.2.2.2.2.1 $$ Hhist
    ihave Hledger' := restoreLedger_keep γ id rs.sn (s := s) (s' := s')
      (by first | exact Href.voteLe.1 | exact Hcv.1.voteLe.1 | exact Hvr.1 | omega)
      (logStoreRec_ksn Hfr.2.2.2.2.2.1) (by first | exact Href.commit_mono | exact Hcv.commit | exact Hc) (by first | exact Href.snapQueue | exact Hcv.queue | exact Hcv.1.snapQueue) $$ Hledger
    ihave #Hsloc' := snapLocOk_keep γ id (.inl Hfr.2.2.2.1) $$ Hsloc
    · iapply ownRawNodeAt_intro γ rn id rs (toPState s') qs (uint.nat s'.logst.inprogress - 1) sc
        s' cf fp rnv sv hprev steps Hwf' Hin Hasync
        (by rw [Hap']; exact Hdlen) (by rw [Hfr.2.2.1]; exact Hunp)
        (by rw [Hfr.2.2.2.1]; exact Hsnap)
        (stepsOk_mono s s' _ Hfr.1 ⟨Hfr.2.2.2.2.1, (logStoreRec_stored Hfr.2.2.2.2.2.1)⟩ Hc Hap'
          (tc_le_of_gh Hfr.2.2.2.2.2.2.2.2.1) Hstok)
        (by rw [Hfr.1]; exact Htrm) (by rw [Hfr.2.2.2.2.2.2.1]; exact ⟨Hstor.1, by rw [Hsn1.2, Hfr.2.2.2.2.2.2.2.2.1, ← Hns0.2]; exact Hstor.2⟩)
        (Hpvoff.keep rfl rfl Hfr.2.2.2.2.2.2.2.1 Hfr.2.2.2.2.2.2.2.2.1 Hfr.1 Hfr.2.2.2.2.2.2.2.2.2.1 Hfr.2.2.2.1
          (PreGuardF.step (Htm (by msg_ne))))
        (by rw [Hfr.2.2.2.2.2.2.2.2.1]; exact Hrs_out) (by rw [Hfr.2.2.2.2.2.2.2.2.1]; exact Hrs_unst)
        (Int.le_trans Hrs_clb Hc)
        (RNFl.keep Hrnfl Hfr.2.2.2.2.2.2.2.2.2.2.1 Hfr.2.2.2.2.2.2.2.2.2.2.2 Hap')
        (Hloan.keep Hfr.2.2.2.2.2.2.2.2.1 Hfr.2.2.2.1 Hfr.2.2.2.2.2.2.2.2.2.2.1 (logStoreRec_stored Hfr.2.2.2.2.2.1) Hfr.2.2.1 Hap' Hc)
        (Hsdt.ofRec Hfr.2.2.2.1 Hfr.2.2.2.2.2.1) Hrole
        (Hphs.keep rfl rfl rfl (HsLe.of_step Href.voteLe Hc) Hfr.2.2.2.1 (.inl Hfr.2.1)) rfl (by omega)
        (by rw [LocalFrame.ns Hfr]; exact Hgtr) (by rw [LocalFrame.ns Hfr]; exact Hglq)
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' Hhist' Hledger' [Hdur] Hrntr Hsc
      · iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hfr.2.2.2.1 Hfr.2.2.2.2.1 (logStoreRec_stored Hfr.2.2.2.2.2.1) $$ Hdur
    isplitl [Herr]
    · icases Herr with (%Herr | ⟨-, #Hd⟩)
      · ileft; ipureintro; exact Herr
      · iright; iexact Hd
    ipureintro
    intro h
    have Hg := (Hlifted h).2
    refine ⟨by rw [← Hps]; exact (Hlifted h).1.of_ids (Hlift h).2.2, ?_⟩
    have := ip_of_logGrow Hg (by
      have := Hipf.1.2; rw [Hp0 h] at this; rw [List.length_append]; push_cast; omega)
    rw [Hip, Nat.add_sub_cancel] at this
    rw [← Hps]
    exact this))

/-- **`RawNode.Propose`, strengthened** (`RawNode.Propose.absSpec`). -/
theorem RawNode.Propose.wp_absProof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    RawNode.Propose.absSpec (GF := GF) (hG := hG) := by
  have wp_raft_StepNs := raft.Step.untracedNs wp_raft_Step
  have wp_raft_Step := raft.Step.untraced wp_raft_Step
  intro sc γ rn id rs ps qs ip data_sl data HtrG
  wp_start as H
  iNamed H
  iNamed Hrn
  -- the scope's facts at the start state
  icases rnScopeAt_scope sc rs s $$ Hsc with ⟨%Hscope, Hsc⟩
  icases ownRaftPhysC_precand cf rnv.raft' id s $$ Hphys with ⟨%Hpre0, Hphys⟩
  icases ownRaftPhysC_ipFacts cf rnv.raft' id s $$ Hphys with ⟨%Hipf, Hphys⟩
  icases ownRaftPhysC_trkDoms cf rnv.raft' id s $$ Hphys with ⟨%Hdom, Hphys⟩
  icases ownRaftPhysC_ackScope cf rnv.raft' id s $$ Hphys with ⟨%Hal0, Hphys⟩
  icases ownRaftPhysC_cq cf rnv.raft' id s $$ Hphys with ⟨#Hcq0, Hphys⟩
  icases ownStepGhost_followerVotes γ _ cf id s $$ Hghost with ⟨%Hfv, Hghost⟩
  icases rnScopeAt_cfgIn sc rs s $$ Hsc with ⟨%Hcin, Hsc⟩
  icases ownStepGhost_cfgScope γ rs fp _ cf id s $$ Hghost with ⟨%Hcfm, Hghost⟩
  have Hlift : sc = true → LiftScope cf id s ∧ AckScope cf ∧ cf.ids = (rnCfg γ).ids := fun h => by
    have Hs := Hscope h
    obtain ⟨HC, Hid⟩ := cfgScope_of Hs (Hcin h) Hcfm
    have Hv : cf.voters = γ.reCfg := HC.voters
    exact ⟨liftScope_of Hs Hpre0 Hfv Hdom.1 Hdom.2 (by rw [Hv]; exact Hid), Hal0 HC.2.1,
      HC.ids ((Hcin h).learners Hcfm)⟩
  have Hp0 : sc = true → uint.Z s.logst.prev.index' = 0 := fun h => by
    rw [(Hscope h).2.2.2.2.2.1]; rfl
  wp_auto_lc 1
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 2) as %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
  icases ownRaftPhysC_sn cf rnv.raft' id s $$ Hphys with ⟨%Hns0, Hphys⟩
  wp_apply wp_slice_literal_ex (V := Loc)
  wp_alloc l0 as Hl0
  wp_auto
  iexists [l0]
  isplitr
  · ipureintro; rfl
  iintro %slp ⟨Hsl, Hsl_cap⟩
  have Hsz : go.arrayLiteralSize [KeyedElement none (ElementLiteralValue
      [KeyedElement (some (KeyField go!"Data")) (ElementExpression go.byte.SliceType #data_sl)])] = 1 := rfl
  simp only [Hsz]
  icases ownStepGhost_certLink γ _ cf id s $$ Hghost with ⟨#Hlink, Hghost⟩
  iunfold certLink at Hlink
  icases Hlink with ⟨-, -, %Hszl, %Hmb⟩
  have Hdsz : s.gh.sn.sz = true → (propEntryM data).Data'.length ≤ entBytesMax := fun hs => by
    rw [Hszl] at hs
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hs
    have := Hmd b hb; have := (Hmb b hb).1
    simp only [propEntryM, entBytesMax]; omega
  imod entRZ_of_struct s.gh.sn.sz l0 (⟨zero_val _, null, null, null, data_sl, slice.nil, 0⟩ : raftpb.Entry)
      (propEntryM data) ⊤ rfl Hdsz $$ [Hl0] with #He
  · iframe Hl0
    simp only [propEntryM]
    iframe Hdata
    repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
    iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  wp_auto
  imod cellRO_alloc $$ «$v1» with #cFr
  ihave #Hnilb := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
  imod msgInC_of_struct s.gh.sn.sz «$a0_ptr» (⟨zero_val _, pty, null, «$v1_ptr», null, null, null,
      slice.mk slp (W64 1) (W64 1), null, null, null, null, null, slice.nil, slice.nil, slice.nil,
      0⟩ : raftpb.Message) (DFrac.own 1) [l0]
      ⟨{ (zero_val MessageM) with Type' := W32 2, From' := id }, [propEntryM data], none, [], []⟩
      ⊤ rfl rfl rfl rfl rfl (fun _ => ⟨by simp, by simp [entBytesMax]⟩) $$ [«$a0» Hsl] with Hm
  · iframe «$a0» Hsl Hnilb cTy cFr
    msg_nulls
    isplitl []
    · iapply (BigSepL2.bigSepL2_singleton (Φ := fun _ p e => entRZ (GF := GF) s.gh.sn.sz p e)).2
      iexact He
    iapply ownSlice_nil
  have HmC : needsCap ({ (zero_val MessageM) with Type' := W32 2, From' := id } : MessageM) = false := rfl
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  -- `raft.Step`: in the scope at the no-snapshot flag, outside it untraced; afterwards the same, with
  -- the step's end state (in the scope) as `Hx`
  by_cases hsc : sc = true
  · icases rnScopeAt_cap hsc rs s $$ Hsc with ⟨#Hcap, Hsc⟩
    wp_apply wp_raft_StepNs cf _ γ _ id s «$a0_ptr» ({ (zero_val MessageM) with Type' := W32 2, From' := id } : MessageM)
      [propEntryM data] [] none []
      (by simp [StepMsg, stepMsgTypes, MsgProp])
      (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne)
      (by msg_ne)
      (fun _ => ⟨rfl, .inr rfl⟩) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
      (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
      (by tr_none) (Hlift hsc).2.1 $$ [$Hphys $Hghost $Hlc1 Hm Htk Hcr]
    · prop_frame
      isplitr
      · imodintro
        iintro %Hc
        simp [MsgSnap] at Hc
      isplitr
      · iexact Hcap
      isplitr
      · ipureintro; exact Hp0 hsc
      · ipureintro; exact (Hscope hsc).2.2.2.2.2.2.2.1
    simp only [MsgProp]
    iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hc', %Hloc, %_, %_, %Htm, %_, -, -, Herr,
      %Hend, -, %Hns', -⟩
    have Hx : sc = true → StepEnd cf id ({ (zero_val MessageM) with Type' := W32 2, From' := id } : MessageM)
        [propEntryM data] [] s s' ∧ NoSnapL s'.outbox := fun _ => ⟨Hend, Hns'⟩
    prop_tail
  · wp_apply wp_raft_Step cf _ γ _ id s «$a0_ptr» ({ (zero_val MessageM) with Type' := W32 2, From' := id } : MessageM)
      [propEntryM data] [] none []
      (by simp [StepMsg, stepMsgTypes, MsgProp])
      (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne)
      (by msg_ne)
      (fun _ => ⟨rfl, .inr rfl⟩) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
      (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
      (by tr_none) $$ [$Hphys $Hghost $Hlc1 Hm Htk Hcr]
    · prop_frame
      · imodintro
        iintro %Hc
        simp [MsgSnap] at Hc
    simp only [MsgProp]
    iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hc', %Hloc, %_, %_, %Htm, %_, -, -, Herr⟩
    have Hx : sc = true → StepEnd cf id ({ (zero_val MessageM) with Type' := W32 2, From' := id } : MessageM)
        [propEntryM data] [] s s' ∧ NoSnapL s'.outbox := fun h => absurd h hsc
    prop_tail

end proof

end EtcdGrove
end Perennial
