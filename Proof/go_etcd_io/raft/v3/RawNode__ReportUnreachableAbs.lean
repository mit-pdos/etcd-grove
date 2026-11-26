/-
Antithesis parity B1, phase 2 (#33, `notes/antithesis-parity-design.md` §4). **`RawNode.ReportUnreachable`,
the strengthened triple** (`RawNode.ReportUnreachable.absSpec`, `RawNodeAbsSpecs.lean`). The proof is
`RawNode__ReportUnreachable.lean`'s, over `ownRawNodeAt` at a mode `md` without snapshots or configuration
changes: the message `pb.Message{Type: MsgUnreachable, From: to}` built as before, then `raft.Step` at the
no-snapshot flag (`raft.Step.untracedNs`), whose end state (`StepEnd`) is the start state but for
`Progress` values of the same `Match` (`unreachEnd`: a leader's `pr.BecomeProbe()`, nothing queued), so the
`RState` reading and the scope are the start state's.
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__ReportUnreachable
public import Spec.go_etcd_io.raft.v3.raft__Step
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasRawnodeR
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Proof.go_etcd_io.raft.v3.TracedUntracedRaftStep
public import Proof.go_etcd_io.raft.v3.RaftStepNoSnap
public import Proof.go_etcd_io.raft.v3.RawNodeAtScope
public import Proof.go_etcd_io.raft.v3.RawNodeReadyAt
public import Proof.go_etcd_io.raft.v3.StepEndIp
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgRest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess


section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- A report's end state has the start state's `RState` reading. -/
theorem toRState_prvals_eq (rs : RNState) (fp : List EntryM) (s : NState) (pvs : GMap w64 Progress)
    (hpm : prvalsMatch pvs = prvalsMatch s.prvals) :
    toRState rs fp { s with prvals := pvs } = toRState rs fp s := by
  unfold toRState
  rw [toPState_prvals s pvs (fun _ => hpm)]
  rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A premise of `Step` about another message type. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex,
  MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow,
  MsgTransferLeader] at Hc))

set_option hygiene false in
/-- `m.Type' = MsgUnreachable` (`hu`) refutes a hypothesis `h` about another type. -/
local macro "unr_absurd" : tactic => `(tactic| (rw [hu] at h; simp [MsgUnreachable, MsgHup, MsgBeat,
  MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgSnap, MsgHeartbeat, MsgHeartbeatResp,
  MsgSnapStatus, MsgCheckQuorum, MsgTransferLeader, MsgTimeoutNow, MsgReadIndex, MsgReadIndexResp,
  MsgPreVote, MsgPreVoteResp, MsgStorageAppendResp, MsgStorageApplyResp, MsgForgetLeader] at h))

set_option maxHeartbeats 1000000 in
/-- **The end state of a report** (`StepEnd`): `s` but for `Progress` values of the same `Match` (a
leader's `BecomeProbe`); nothing queued. (`TracedRaftStepUnreach.lean`'s `unreach_end`, restated here
so that the untraced cone does not import the traced bundle.) -/
theorem unreachEnd {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hu : m.Type' = MsgUnreachable) (hT0 : m.Term' = W64 0)
    (h : StepEnd c id m ents ctx s s') :
    ∃ pvs : GMap w64 Progress, prvalsMatch pvs = prvalsMatch s.prvals ∧
      s' = { sendMsgs s [] with prvals := pvs } := by
  have hnbf : ¬ PreBF m s := by
    unfold PreBF; rw [hT0]; intro h'; have := h'.1; simp at this
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hety : StepEndTy m.Type' := by unfold StepEndTy; simp [hu]
  have hnh : m.Type' ≠ MsgHup := fun h => by unr_absurd
  have hnv : m.Type' ≠ MsgVote := fun h => by unr_absurd
  have hnp : m.Type' ≠ MsgProp := fun h => by unr_absurd
  have hself : s = { sendMsgs s [] with prvals := s.prvals } := by cases s; simp [sendMsgs]
  obtain ⟨pvs0, hfn⟩ := (h hety (by xtrec_tac)).2.2.2 (fun h' => h'.1 hT0) hnh hnv
  rw [hpre pvs0] at hfn
  obtain ⟨hf, hc, hl⟩ := hfn
  cases hr : s.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    obtain ⟨-, -, he⟩ := StepProof.followerStepResult_rnoop c id s m ents sv d s' ctx (.inr (.inl hu)) hres
    exact ⟨s.prvals, rfl, by rw [he]; exact hself⟩
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    obtain ⟨-, -, he⟩ :=
      StepProof.candidateStepResult_rest c id s m ents sv d s' ctx (.inr (.inr (.inl hu))) hres
    exact ⟨s.prvals, rfl, by rw [he]; exact hself⟩
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    obtain ⟨-, -, he⟩ :=
      StepProof.candidateStepResult_rest c id s m ents sv d s' ctx (.inr (.inr (.inl hu))) hres
    exact ⟨s.prvals, rfl, by rw [he]; exact hself⟩
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC at hres
    rw [if_neg hnp] at hres
    obtain ⟨-, hres⟩ := hres
    unfold LeaderNonpropResultC at hres
    rcases hres with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
      ⟨-, lt', ms, pvs, rfl, -, hpm, hun⟩ | ⟨h, -⟩
    rotate_right 2
    · obtain ⟨rfl, rfl⟩ := hun hu
      exact ⟨pvs, hpm, rfl⟩
    all_goals exfalso
    all_goals unr_absurd

/-- **`RawNode.ReportUnreachable`, strengthened** (`RawNode.ReportUnreachable.absSpec`). -/
theorem RawNode.ReportUnreachable.wp_absProof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    RawNode.ReportUnreachable.absSpec (GF := GF) (hG := hG) := by
  have wp_raft_StepNs := raft.Step.untracedNs wp_raft_Step
  intro md hsn hcc γ rn id rs ps qs ip to HtrG
  wp_start as H
  iNamed H
  iNamed Hrn
  -- the scope at `md`: no snapshot (the storage's cap, the boundary `0`, no `MsgSnap` queued) and,
  -- without configuration changes, no outgoing half, so no automatic leave (`AckScope`)
  icases rnScopeAt_someMd md rs s $$ Hsc with ⟨%Hscp, #Hcap0, Hsc⟩
  ihave #Hcap := Hcap0 $$ %hsn
  obtain ⟨Hrsc, Hcin, -, -⟩ := Hscp
  obtain ⟨-, Hprev, -, Hnsq⟩ := Hrsc.2.2.2.2.1 hsn
  icases ownRaftPhysC_ackScope cf rnv.raft' id s $$ Hphys with ⟨%Hal0, Hphys⟩
  icases ownStepGhost_cfgScope γ rs fp _ cf id s $$ Hghost with ⟨%Hcfm, Hghost⟩
  have Hal : AckScope cf := by
    have hd := Hcin.2.2.2
    have ho := Hrsc.1 hcc hd
    rw [Hcfm.2 hd] at ho
    exact Hal0 ho
  have Hp0 : uint.Z s.logst.prev.index' = 0 := by rw [Hprev]; rfl
  wp_auto_lc 1
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 10) as %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  imod cellRO_alloc $$ «$v1» with #cFr
  imod msgOwn_lit0 «$a0_ptr» _ ({ (zero_val MessageM) with Type' := W32 10, From' := to } : MessageM) ⊤ $$ [«$a0»] with Hm
  · iframe «$a0» cTy cFr
    isplitr
    · ipureintro; simp
    msg_nulls
  ihave Hm := msgOwn_to_msgIn _ _ (by simp [MsgApp]) $$ Hm
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.guard rs.capplied rs.cfg (ds := ds)) $$ Hphys with ⟨%Hpf, Hphys⟩
  icases ownRaftPhysC_sn cf rnv.raft' id s $$ Hphys with ⟨%Hns0, Hphys⟩
  wp_apply wp_raft_StepNs cf _ γ _ id s «$a0_ptr» ({ (zero_val MessageM) with Type' := W32 10, From' := to } : MessageM) [] [] none []
    (by simp [StepMsg, stepMsgTypes, MsgUnreachable])
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (⟨fun _ => rfl, fun h => absurd h (by msg_ne), fun h => absurd h (by msg_ne)⟩ : RestMsgOk s _ [] []) Hwf
    (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
    (by tr_none) Hal $$ [$Hphys $Hghost $Hlc1 Hcr Hm]
  · -- the message: no entries, no `Context`, no snapshot
    have hP : (W32 10 : w32) ≠ MsgProp := by simp [MsgProp]
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
      rw [show mtypeOf (W32 10) = none from rfl] at Hty
      cases Hty
    isplitl [Hcr]
    · rw [ite_eq_right (by msg_ne)]; iexact Hcr
    isplitr
    · imodintro
      iintro %Hc
      simp [MsgSnap] at Hc
    isplitr
    · iexact Hcap
    isplitr
    · ipureintro; exact Hp0
    · ipureintro; exact Hnsq
  have hP : (W32 10 : w32) ≠ MsgProp := by simp [MsgProp]
  simp only [hP]
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, -, %Htm, -, -, -, Herr,
    %Hend, -, %Hns', -⟩
  -- the end state: `s` but for the `Progress` values, of the same `Match`
  obtain ⟨pvs, Hpm, Hse⟩ := unreachEnd (s := s) (s' := s') rfl rfl Hend
  rw [ie_sendMsgs_nil] at Hse
  have Hc := Href.commit_mono
  have e1 := Href.keep (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne)); subst e1
  have e2 := Hcc (by msg_ne); subst c'
  wp_auto
  obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩ := Hfr (by msg_ne) (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne)) (fun h => absurd h (by msg_ne))
  icases ownRaftPhysC_sn cf rnv.raft' id s' $$ Hphys with ⟨%Hsn1, Hphys⟩
  obtain ⟨Ht1, -, Ht3, Hip4, -, Hpcs⟩ := Htm (by msg_ne)
  have Htrm' : rs.term = s'.term := by rw [Htrm, Hse]
  ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Hip4 (by msg_ne)) $$ Hstrecs
  -- the scope and the reading kept
  ihave Hsc := rnScopeAt_keepAll (some md) rs rs s s' (fun _ h => by rw [Hse]; exact h.with_prvals pvs Hpm)
    (by rw [Hse]) (hfl := by rw [Hse]; exact ⟨rfl, rfl, rfl⟩)
    (hx := by rw [Hse]; exact ⟨rfl, rfl, rfl⟩) $$ Hsc
  ihave Hrntr := rnTrace_none (GF := GF) γ rnv.raft' id cf rs.delivered s'
    (by rw [Hgh]; exact Hgtr.trans HtrG)
  have Hps' : toRState rs fp s' = ps := by rw [Hse, toRState_prvals_eq rs fp s pvs Hpm]; exact Hps
  have Hip' : uint.nat s'.logst.inprogress = ip + 1 := by rw [Hse]; exact Hip
  icases Herr with (%Herr | ⟨%Hc', -⟩)
  · iapply HΦ
    simp only [named]
    ihave #Hhist' := restoredSnapHistory_keep γ id Hsd $$ Hhist
    ihave Hledger' := restoreLedger_keep γ id rs.sn (s := s) (s' := s')
      (by first | exact Href.voteLe.1 | exact Hcv.1.voteLe.1 | exact Hvr.1 | omega)
      (logStoreRec_ksn Hsd) (by first | exact Href.commit_mono | exact Hcv.commit | exact Hc) (by first | exact Href.snapQueue | exact Hcv.queue | exact Hcv.1.snapQueue) $$ Hledger
    ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
    iapply ownRawNodeAt_intro γ rn id rs ps qs ip (some md) s' cf fp rnv sv hprev steps Hwf' Hin
      Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
      (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, (logStoreRec_stored Hsd)⟩ Hc Ha (tc_le_of_gh Hgh) Hstok) Htrm'
      (by rw [Hsg]; exact ⟨Hstor.1, by rw [Hsn1.2, Hgh, ← Hns0.2]; exact Hstor.2⟩)
      (Hpvoff.step rfl rfl Hpre Hgh (by rw [← Htrm', Htrm]; exact Hpvoff.2.2.1) Hpcs
          (by msg_ne))
      (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
      (RNFl.keep Hrnfl Hfl' Hap' Ha) (Hloan.keep Hgh Hsn Hfl' (logStoreRec_stored Hsd) Hu Ha Hc)
      (Hsdt.ofRec Hsn Hsd) Hrole
      (Hphs.keep rfl rfl rfl (HsLe.of_step Href.voteLe Hc) Hsn (.inl (Hip4 (by msg_ne)))) Hps' Hip'
      (by rw [Hgh]; exact Hgtr) (by rw [Hgh]; exact Hglq)
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' Hhist' Hledger' [Hdur] Hrntr Hsc
    · -- (durability stage II (i)) the step keeps `durTie`'s fields
      iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hsn Hpv (logStoreRec_stored Hsd) $$ Hdur
  · exfalso; revert Hc'; msg_ne

end proof

end EtcdGrove
end Perennial
