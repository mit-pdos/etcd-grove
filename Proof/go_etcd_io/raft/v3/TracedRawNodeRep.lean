/-
Lean-first (no Rocq counterpart). **`RawNode.ReportUnreachable` at a traced node** (2026-11-11,
trace-check Q8 stage 1 slice 27n, Q27 (a); `notes/decisions.md`, "Q8 stage 1 (slice 27n)").
Raft-internal (not on `etc/api/raft.txt`).

`RawNode.ReportUnreachable.spec`'s triple at a traced cluster (`γ.reTrace = some γd`), with the bounds
the traced bundle's premises read (as `RawNode.Tick.spec`'s traced premise); the proof is
`RawNode.ReportUnreachable.wp_proof`'s with `raft.Step.spec` at the resources the traced bundle on
`UnreachPath` (`TracedRaftStepUnreach.lean`) gives, the capability opened from `rnTrace` and closed
idle at the end state (a report logs no line).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRawNode
public import Proof.go_etcd_io.raft.v3.TracedRaftStepUnreach
public import Spec.go_etcd_io.raft.v3.RawNode__ReportUnreachable
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasRawnodeR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section traced
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

/-- **`RawNode.ReportUnreachable` at a traced node**: the untraced spec's triple with `γ.reTrace = some
γd` for `= none`, and the bounds the traced bundle's premises read: the term ceiling below the traced
numbers' bound, the receipts' fit. -/
abbrev RawNode.ReportUnreachable.tracedTriple : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (to : w64) (γd : GName),
  γ.reTrace = some γd →
  uint.Z rs.tc + 1 < traceNumBound →
  receiptBound GF + γ.reBoot.length ≤ traceNumBound →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"ReportUnreachable")) (Val #to))
  {{ RET #(); "Hrn" ∷ ownRawNode γ rn id rs }}

/-- See `RawNode.ReportUnreachable.tracedTriple`; hypothesis: the traced bundle on `UnreachPath`. -/
theorem RawNode.ReportUnreachable.traced
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG))
    (hb : stepBundle_traced.on (GF := GF) (hG := hG) UnreachPath) :
    RawNode.ReportUnreachable.tracedTriple (GF := GF) (hG := hG) := by
  intro γ rn id rs to γd HtrG Htcb Hfit
  wp_start as H
  iNamed H
  iNamed Hrn
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
  -- the capability, open; the bundle's premises from the node's state
  have Htr : s.gh.tr = some γd := Hgtr.trans HtrG
  icases (rnTrace_some γ rnv.raft' id cf rs.delivered s γd Htr).1 $$ Hrntr with
    ⟨%Hscope, %Hpure, #Hcqf, #Hnosnap, %bt, %Hbt, Hcap⟩
  imod trNoSnap_prev0 s.gh.tr s.logst (by rw [Htr]; simp) $$ Hnosnap with %Hprev0
  icases ownRaftPhysC_cq cf rnv.raft' id s $$ Hphys with ⟨#Hcq, Hphys⟩
  icombine Hcqf Hcq gives %Hcqe
  icases ownRaftPhysC_dom cf rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
  icases ownRaftPhysC_precand cf rnv.raft' id s $$ Hphys with ⟨%Hpcd, Hphys⟩
  have Hst1 : uint.Z s.term ≤ uint.Z rs.tc := by rw [Hpvoff.2.1]; exact Hpvoff.2.2.1
  have Hmt : mtypeOf (W32 10) = none := rfl
  ihave Hpre : (trCapB s.gh.tr γ rnv.raft' id cf bt (fun C => SimIdle C s) (fun _ => True) ∗
      (recvTokOf γd ({ (zero_val MessageM) with Type' := W32 10, From' := to } : MessageM) [] [] ∗
        □ (∀ ty : MsgType, ⌜mtypeOf (W32 10) = some ty ∧ ty.traced = true⌝ -∗
          isMessageC γ (absMsg ty ({ (zero_val MessageM) with Type' := W32 10, From' := to } : MessageM)
            [] []))) ∗
      TrNoSnap s.gh.tr s.logst : IProp GF) $$ [Hcap]
  · iframe Hcap Hnosnap
    isplitl
    · iunfold recvTokOf
      iintro %ty %h
      rw [Hmt] at h; cases h.1
    imodintro
    iintro %ty %h
    rw [Hmt] at h; cases h.1
  imod hb γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf rnv.raft' id s
      ({ (zero_val MessageM) with Type' := W32 10, From' := to } : MessageM) [] none [] [] γd
      (fun _ => True) bt ⟨rfl, rfl⟩ Htr Hscope.1 Hcqe.symm
      (by unfold StepEndTy; simp [MsgUnreachable]) Hwf (fun _ => rfl) (fun h => absurd h (by msg_ne))
      (fun ty h => by rw [Hmt] at h; cases h)
      (by omega) (by show uint.Z (W64 0) < traceNumBound; unfold traceNumBound; decide)
      (fun ty h => by rw [Hmt] at h; cases h)
      Hfit Hscope.2 Hsub
      (fun h => by have := Hpcd h; rw [Hscope.1] at this; cases this)
      ⟨fun h => absurd h (by msg_ne), fun h => absurd h (by msg_ne),
        fun h => by rcases h with h | h | h <;> exact absurd h (by msg_ne),
        fun ty h => by rw [Hmt] at h; cases h⟩
      (fun h => by rcases h with h | h <;> exact absurd h (by msg_ne)) $$ Hpre
    with ⟨%R, HG, Hgates, Hclose⟩
  wp_apply wp_raft_Step cf _ γ _ id s «$a0_ptr» ({ (zero_val MessageM) with Type' := W32 10, From' := to } : MessageM) [] [] none [] R
      (fun s' => iprop(⌜OutTyStep s s'⌝ ∗ ∃ bt' : Bool, ⌜bt = true → bt' = true⌝ ∗
        trCapB s.gh.tr γ rnv.raft' id cf bt' (fun C => SimIdle C s') (stepLastEv (fun _ => True))))
    (by simp [StepMsg, stepMsgTypes, MsgUnreachable])
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (⟨fun _ => rfl, fun h => absurd h (by msg_ne), fun h => absurd h (by msg_ne)⟩ : RestMsgOk s _ [] []) Hwf
    (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
    (fun h => absurd h (by msg_ne)) (fun h => absurd h (by msg_ne)) (fun h => absurd h (by msg_ne))
    (fun h => absurd h (by msg_ne))
    (fun h => absurd h (by msg_ne)) (fun h => absurd h (by msg_ne)) $$ [$Hphys $Hghost $Hlc1 Hcr Hm HG Hgates Hclose]
  · -- the message: no entries, no `Context`, no snapshot
    have hP : (W32 10 : w32) ≠ MsgProp := by simp [MsgProp]
    simp only [hP, ↓reduceIte, named]
    isplitr
    · imodintro
      iintro %h
      exact absurd h.1 (by msg_ne)
    isplitl [Hm]
    · iframe Hm
      repeat (isplitr; · first | iempintro | (ipureintro; simp) | (ipureintro; msg_ne))
      imodintro
      iintro %ty %Hty
      rw [Hmt] at Hty
      cases Hty
    isplitl [Hcr]
    · rw [ite_eq_right (by msg_ne)]; iexact Hcr
    isplitr
    · imodintro
      iintro %Hc
      simp [MsgSnap] at Hc
    iframe HG Hgates Hclose
  have hP : (W32 10 : w32) ≠ MsgProp := by simp [MsgProp]
  simp only [hP]
  iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Href, %Hcc, -, %Hfr, -, %Htm, -, -, -, Herr, HG⟩
  have Hc := Href.commit_mono
  have e1 := Href.keep (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne)); subst e1
  have e2 := Hcc (by msg_ne); subst c'
  wp_auto
  obtain ⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩ := Hfr (by msg_ne) (by msg_ne) (by msg_ne) (fun h => absurd h (by msg_ne))
  icases ownRaftPhysC_sn cf rnv.raft' id s' $$ Hphys with ⟨%Hsn1, Hphys⟩
  obtain ⟨Ht1, -, Ht3, Hip4, -, Hpcs⟩ := Htm (by msg_ne)
  have Ht3 := Ht3 (by msg_ne) (by msg_ne) (by msg_ne)
  have H0 : uint.Z (zero_val MessageM).Term' = 0 := rfl
  simp only [H0] at Ht3
  have Htrm' : rs.term = s'.term := by
    rw [Htrm]
    have h0 : 0 ≤ uint.Z s.term := by word
    have h2 : uint.Z s'.term ≤ uint.Z s.term := by
      omega
    word
  ihave #Hstr' := ackInv_keep (rs' := rs) γ rfl Hstok Ht1 Hpv Hsn (logStoreRec_stored Hsd) (Hip4 (by msg_ne)) $$ Hstrecs
  -- the capability back, idle at the end state
  have Htr' : s'.gh.tr = some γd := by rw [Hgh]; exact Htr
  -- (2026-11-12, implementation step 3) the leader exclusion's clause at the end state
  icases ownStepGhost_bootCommit γ _ cf id s' $$ Hghost with ⟨%Hbc', Hghost⟩
  icases ownStepGhost_bootPrefix γ _ cf id s' $$ Hghost with ⟨%Hbp', Hghost⟩
  ihave #Hnosnap' := trNoSnap_logst s.gh.tr s'.gh.tr s.logst s'.logst (by rw [Htr', Htr])
    Hpv.symm Hsg.symm $$ Hnosnap
  have Hprev' : uint.Z s'.logst.prev.index' = 0 := by rw [Hpv]; exact Hprev0
  have Hboot' := RnTrBoot.step Hpure.2.2.2 Hpcs.2.2.hup Hap' Hprev' (Hbp' Hprev') Hbc'
  icases HG with ⟨%Houtty, %bt', %Hmono, HG⟩
  ihave Hrntr : rnTrace γ rnv.raft' id cf rs.delivered s' $$ [HG]
  · iapply (rnTrace_some γ rnv.raft' id cf rs.delivered s' γd Htr').2
    isplitr
    · ipureintro; exact ⟨Hpre.trans Hscope.1, Hscope.2⟩
    isplitr
    · ipureintro; exact Hpure.step (by rw [Htr]; rfl) Houtty Hboot'
    isplitr
    · iexact Hcqf
    isplitr
    · iapply trNoSnap_logst s.gh.tr s'.gh.tr s.logst s'.logst (by rw [Htr', Htr]) Hpv.symm Hsg.symm
        $$ Hnosnap
    iexists bt'
    isplitr
    · ipureintro; exact fun h => Hmono (Hbt h)
    rw [show s'.gh.tr = s.gh.tr by rw [Htr', Htr]]
    iapply trCapB_monoΛ _ γ rnv.raft' id cf bt' _ _ _ (fun _ _ => trivial) $$ HG
  icases Herr with (%Herr | ⟨%Hc', -⟩)
  · iapply HΦ
    simp only [named]
    ihave #Hsloc' := snapLocOk_keep γ id (.inl Hsn) $$ Hsloc
    iapply ownRawNode_intro_tr γ rn id rs s' cf fp rnv sv hprev steps Hwf' Hin
      Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
      (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, (logStoreRec_stored Hsd)⟩ Hc Ha (tc_le_of_gh Hgh) Hstok) Htrm' (by rw [Hsg]; exact ⟨Hstor.1, by rw [Hsn1.2, Hgh, ← Hns0.2]; exact Hstor.2⟩)
      (Hpvoff.step rfl rfl Hpre Hgh (by rw [← Htrm', Htrm]; exact Hpvoff.2.2.1) Hpcs
          (by msg_ne))
      (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
        (RNFl.keep Hrnfl Hfl' Hap' Ha) (Hloan.keep Hgh Hsn Hfl' (logStoreRec_stored Hsd) Hu Ha Hc)
      (Hsdt.ofRec Hsn Hsd) Hrole
        (Hphs.keep rfl rfl rfl (HsLe.of_step Href.voteLe Hc) Hsn (.inl (Hip4 (by msg_ne))))
        (by rw [Hgh]; exact Hgtr) (by rw [Hgh]; exact Hglq)
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr' Hloanc Hsloc' [Hdur] Hrntr
    · iapply durTie_congr γ (rs := rs) (s := s) (by rfl) (by rfl) Hsn Hpv (logStoreRec_stored Hsd) $$ Hdur
  · exfalso; revert Hc'; msg_ne

end traced

end EtcdGrove
end Perennial
