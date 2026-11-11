/-
Lean-first (no Rocq counterpart). Q8 stage 1, slice 7 (2026-11-10): the untraced instances of the
handlers below `raft.Step`, one spec for both modes since slice 7 (`notes/decisions.md`, "Q8 stage 1
(slice 7)"), as `TracedUntraced.lean`'s: each `X.untraced : X.spec → X.untracedTriple`, the statement
before slice 7 (`s.gh.tr = none`, no gate), from the one spec with the gates the struct's nil logger
(`ownRaftPhysC_traceLogger`, `hookGateOpt_none`) and `G := emp`, for the callers that stay untraced.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedUntraced
public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__handleAppendEntries
public import Spec.go_etcd_io.raft.v3.raft__campaign
public import Spec.go_etcd_io.raft.v3.raft__hup
public import Spec.go_etcd_io.raft.v3.stepCandidate
public import Spec.go_etcd_io.raft.v3.stepFollower
public import Spec.go_etcd_io.raft.v3.stepLeader

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section untraced
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `raft.handleHeartbeat.spec` at an untraced node (the statement before slice 7). -/
abbrev raft.handleHeartbeat.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (dq dqe : DFrac) (cap : Bool)
    (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (cl : List w8) (rs : List Loc),
  uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) →
  m.From' ≠ id →
  s.term ≠ W64 0 →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgPtsC ml dq dqe cap ⟨m, ents, sn, cl, rs⟩ }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"handleHeartbeat")) (Val #ml))
  {{ RET #(); ownRaftPhysCV c c.voters r id (heartbeatResult id s m cl) ∗
      msgPtsC ml dq dqe cap ⟨m, ents, sn, cl, rs⟩ }}

/-- `raft.handleHeartbeat.spec`'s untraced instance. -/
theorem raft.handleHeartbeat.untraced (h : raft.handleHeartbeat.spec (GF := GF) (hG := hG)) :
    raft.handleHeartbeat.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s ml dq dqe cap m ents sn cl rs Hcommit Hfrom Htz htr
  iintro %Φ ⟨#Hpkg, Hphys, Hm⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s ml dq dqe cap m ents sn cl rs iprop(emp) iprop(emp) Hcommit Hfrom Htz $$ [Hphys Hm]
  · iframe Hpkg Hphys Hm
    isplitr
    · iempintro
    iintro -
    rw [htr]
    iapply hookGateOpt_none r _ tl iprop(emp) Htlok
    iframe Htl
  inext
  iintro ⟨Hphys, Hm, -⟩
  iapply HΦ
  iframe Hphys Hm

/-- `raft.handleAppendEntries.spec` at an untraced node (the statement before slice 7). -/
abbrev raft.handleAppendEntries.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8)
    (rs : List Loc),
  PlogWf (entryID.mk m.LogTerm' m.Index') ents →
  uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 →
  (let ls := s.logst
   let es := ls.sents ++ ls.uents
   uint.Z ls.committed ≤ uint.Z m.Index' →
   PlogMatches ls.prev es (entryID.mk m.LogTerm' m.Index') →
   plogFindConflict ls.prev es ents = W64 0 ∨
   uint.Z ls.committed < uint.Z (plogFindConflict ls.prev es ents)) →
  m.From' ≠ id →
  m.Type' = MsgApp →
  s.role ≠ .leader →
  s.term ≠ W64 0 →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"handleAppendEntries")) (Val #ml))
  {{ (s' : NState), RET #();
      ownRaftPhysCV c c.voters r id s' ∗ ⌜HandleAppResult id s m ents s'⌝ }}

/-- `raft.handleAppendEntries.spec`'s untraced instance. -/
theorem raft.handleAppendEntries.untraced (h : raft.handleAppendEntries.spec (GF := GF) (hG := hG)) :
    raft.handleAppendEntries.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s ml m ents sn ctx rs Hwf Hnw Hconf Hfid Hty Hnl Htz htr
  iintro %Φ ⟨#Hpkg, Hphys, Hm⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s ml m ents sn ctx rs iprop(emp) (fun _ => iprop(emp)) Hwf Hnw Hconf Hfid Hty Hnl Htz $$ [Hphys Hm]
  · iframe Hpkg Hphys Hm
    isplitr
    · iempintro
    iintro %s1 %mm %_ -
    rw [htr]
    iapply hookGateOpt_none r _ tl iprop(emp) Htlok
    iframe Htl
  inext
  iintro %s' ⟨Hphys, %Hres, -⟩
  iapply HΦ $$ %s'
  iframe Hphys
  ipureintro; exact Hres

/-- The untraced gates of `campaign` (and `hup`): the role change's and every send's, from the struct's
nil logger, `G0 := G := emp`. -/
theorem campaignGates_none (c : CfgM) (r : Loc) (id : w64) (s : NState) (t : CampaignType)
    (tl : GoInterface) (htr : s.gh.tr = none) (Htlok : TraceLoggerOk tl) :
    (r.[raft, go!"traceLogger"] ↦□ tl : IProp GF) ⊢
      (iprop(emp) -∗ if t = campaignPreElection then iprop(|={⊤}=> (emp : IProp GF))
        else HookGate s.gh.tr r (NodeEvOf (W64 1) id (becomeCandidate id s) c) iprop(emp)) ∗
      □ (∀ (pvs : GMap w64 Progress) (y : w64) (o : List Msg), ⌜y ∈ c.voters⌝ -∗ iprop(emp) -∗
        HookGateOpt s.gh.tr r
          (sendOutGate id { campRoleState id s (decide (t = campaignPreElection)) with prvals := pvs } c
            (if y = id then vrespW32 (decide (t = campaignPreElection))
             else vreqW32 (decide (t = campaignPreElection)))
            [campMsg (decide (t = campaignPreElection)) id (s.term + W64 1)
              (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) (transferCtx t) y]) iprop(emp)) := by
  iintro #Htl
  rw [htr]
  isplitl
  · iintro -
    split
    · imodintro; iempintro
    · iapply hookGate_none r _ tl iprop(emp) Htlok
      iframe Htl
  · imodintro
    iintro %pvs %y %o %_ -
    iapply hookGateOpt_none r _ tl iprop(emp) Htlok
    iframe Htl

/-- `raft.campaign.spec` at an untraced node (the statement before slice 7). -/
abbrev raft.campaign.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (t : CampaignType),
  s.role ≠ .leader →
  id ∈ c.voters →
  uint.Z s.term + 1 < 2 ^ 64 →
  (t = campaignPreElection → s.prevote = true ∧ uint.Z s.term + 1 ≤ uint.Z s.gh.tc) →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"campaign")) (Val #t))
  {{ (peers : List w64) (pvs : GMap w64 Progress), RET #();
      ⌜peers ≡ₚ elements (c.voters \ {[id]})⌝ ∗
      ownRaftPhysCV c c.voters r id
        { campaignState id s (decide (t = campaignPreElection)) peers (transferCtx t)
            with prvals := pvs } }}

/-- `raft.campaign.spec`'s untraced instance. -/
theorem raft.campaign.untraced (h : raft.campaign.spec (GF := GF) (hG := hG)) :
    raft.campaign.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s t Hrole Hid Hnw Hpv htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  icases campaignGates_none c r id s t tl htr Htlok $$ Htl with ⟨Hgbc, #Hgsend⟩
  iapply h c r id s t iprop(emp) (fun _ => iprop(emp)) Hrole Hid Hnw Hpv (PermInv.const _) $$ [Hphys Hgbc]
  · dsimp only
    iframe Hpkg Hphys Hgbc Hgsend
  inext
  iintro %peers %pvs ⟨%Hp, Hphys, -⟩
  iapply HΦ $$ %peers %pvs
  iframe Hphys
  ipureintro; exact Hp

/-- `raft.hup.spec` at an untraced node (the statement before slice 7). -/
abbrev raft.hup.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (t : CampaignType),
  uint.Z s.term + 1 < 2 ^ 64 →
  (t = campaignPreElection → s.prevote = true ∧ uint.Z s.term + 1 ≤ uint.Z s.gh.tc) →
  NStateWf s →
  uint.Z s.logst.fl ≤ uint.Z s.logst.applied →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"hup")) (Val #t))
  {{ (s' : NState), RET #();
      ownRaftPhysCV c c.voters r id s' ∗ ⌜HupOkC c id s s'⌝ ∗
      ⌜s'.role = .preCandidate → s'.role = s.role ∨ t = campaignPreElection⌝ }}

/-- `raft.hup.spec`'s untraced instance. -/
theorem raft.hup.untraced (h : raft.hup.spec (GF := GF) (hG := hG)) :
    raft.hup.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s t Hnw Hpv Hwf Hfla htr
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  icases campaignGates_none c r id s t tl htr Htlok $$ Htl with ⟨Hgbc, #Hgsend⟩
  iapply h c r id s t iprop(emp) (fun _ => iprop(emp)) Hnw Hpv Hwf Hfla (PermInv.const _) $$ [Hphys Hgbc]
  · dsimp only
    iframe Hpkg Hphys Hgsend
    iintro %_
    iexact Hgbc
  inext
  iintro %s' ⟨Hphys, -, %H1, %H2⟩
  iapply HΦ $$ %s'
  iframe Hphys
  ipureintro; exact ⟨H1, H2⟩

/-- `stepCandidate.spec` at an untraced node (the statement before slice 8). -/
abbrev stepCandidate.untracedTriple : Prop :=
  ∀ (c : CfgM) (scfg : CSLists) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (rs : List Loc) (sv : SnapshotM) (cl : List w8),
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgProp ∨
   m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨
   (m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp ∨
    m.Type' = MsgCheckQuorum) ∨
   m.Type' = MsgSnap ∨ m.Type' = MsgPreVoteResp ∨
   m.Type' = MsgReadIndex ∨
   (m.Type' = MsgReadIndexResp ∨ m.Type' = MsgForgetLeader ∨ m.Type' = MsgTransferLeader ∨
    m.Type' = MsgTimeoutNow ∨ m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus)) →
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgApp ∨
   m.Type' = MsgHeartbeat ∨ m.Type' = MsgSnap →
   m.Term' = s.term ∧ m.Term' ≠ W64 0) →
  s.role = .candidate ∨ s.role = .preCandidate →
  (m.Type' = MsgApp →
     PlogWf (entryID.mk m.LogTerm' m.Index') ents ∧
     uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 ∧
     (let ls := s.logst
      let es := ls.sents ++ ls.uents
      uint.Z ls.committed ≤ uint.Z m.Index' →
      PlogMatches ls.prev es (entryID.mk m.LogTerm' m.Index') →
      plogFindConflict ls.prev es ents = W64 0 ∨
      uint.Z ls.committed < uint.Z (plogFindConflict ls.prev es ents)) ∧
     m.From' ≠ id) →
  (m.Type' = MsgHeartbeat →
     uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) ∧
     m.From' ≠ id) →
  (s.role = .preCandidate → m.Type' = MsgPreVoteResp →
   uint.Z s.term + 1 < 2 ^ 64) →
  (m.Type' = MsgSnap →
     sn = some sv ∧ scfg = sv.Metadata'.ConfState'.lists ∧
     SnapScopeIf id sv scfg ∧ m.From' ≠ id ∧
     s.gh.ns = false) →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgIn ml (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard)
               ⟨m, ents, sn, cl, rs⟩ ∗
      "#Hcert" ∷ rcvSrc s.gh.sn m.Type' sn }}
    (App (App (Val #(functions stepCandidate [])) (Val #r)) (Val #ml))
  {{ (err : GoInterface) (s' : NState) (dropped : Bool) (c' : CfgM), RET #err;
      ownRaftPhysCV c' c'.voters r id s' ∗
      ⌜CandidateStepResultC c scfg id s m ents sv dropped s' c' cl⌝ ∗
      (if dropped then globalAddr ErrProposalDropped ↦□ err
       else ⌜err = interface.nil⌝) }}

/-- `stepCandidate.spec`'s untraced instance: every gate from the struct's nil logger, `G := emp`. -/
theorem stepCandidate.untraced (h : stepCandidate.spec (GF := GF) (hG := hG)) :
    stepCandidate.untracedTriple (GF := GF) (hG := hG) := by
  intro c scfg r id s ml m ents sn rs sv cl Hty Hterm Hrole Happ Hhb Hpvnw Hsnap htr
  iintro %Φ ⟨#Hpkg, Hphys, Hm, #Hcert⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  imod (preceipt_zero (GF := GF)) with #Hrc00
  iapply h c scfg r id s ml m ents sn rs sv cl (fun _ => iprop(emp)) (fun _ => iprop(emp)) iprop(emp)
    iprop(emp) iprop(emp) 0
    Hty Hterm Hrole Happ Hhb Hpvnw
    (fun hs => let ⟨a, b, c', d, e⟩ := Hsnap hs; ⟨a, b, c', d, e, htr⟩)
    (PermInv.const _) (IdxFree.const _ _) (IdxFree.const _ _) $$ [Hphys Hm]
  · dsimp only
    iframe Hpkg Hphys Hrc00 Hm Hcert
    rw [htr]
    isplitr
    · iempintro
    isplitr
    · iintro %_ -
      iapply hookGate_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro %_ %pvs %s1 %mm %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro %_ %pvs -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro %_ -
      iapply hookGate_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro %_ - -
      iapply hookGateN_none r _ 1 tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · imodintro
      iintro %_ %pvs %to %mm %_ %_ %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iapply trNoSnap_none
    isplitr
    · iintro %_ -
      iapply hookGate_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · imodintro
      iintro %_ %pvs %y %_ %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    · iintro %_ -
      iapply hookGate_none r _ tl iprop(emp) Htlok
      iframe Htl
  inext
  iintro %err %s' %dropped %c' ⟨Hphys, %Hres, Herr, -⟩
  iapply HΦ $$ %err %s' %dropped %c'
  iframe Hphys Herr
  ipureintro; exact Hres

/-- `stepFollower.spec` at an untraced node (the statement before slice 8). -/
abbrev stepFollower.untracedTriple : Prop :=
  ∀ (c : CfgM) (scfg : CSLists) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (rs : List Loc) (sv : SnapshotM) (cl : List w8),
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgProp ∨
   m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨
   (m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp ∨
    m.Type' = MsgCheckQuorum) ∨
   m.Type' = MsgSnap ∨ m.Type' = MsgPreVoteResp ∨
   m.Type' = MsgReadIndex ∨
   (m.Type' = MsgReadIndexResp ∨ m.Type' = MsgForgetLeader ∨ m.Type' = MsgTransferLeader ∨
    m.Type' = MsgTimeoutNow ∨ m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus)) →
  (m.Type' = MsgReadIndex → m.Term' = W64 0 ∧ s.lead ≠ id) →
  (m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨ m.Type' = MsgSnap → s.term ≠ W64 0) →
  (m.Type' = MsgProp →
     (m.From' = W64 0 ∨ m.From' = id) ∧
     m.Term' = W64 0 ∧
     s.lead ≠ id) →
  (m.Type' = MsgApp →
     PlogWf (entryID.mk m.LogTerm' m.Index') ents ∧
     uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 ∧
     (let ls := s.logst
      let es := ls.sents ++ ls.uents
      uint.Z ls.committed ≤ uint.Z m.Index' →
      PlogMatches ls.prev es (entryID.mk m.LogTerm' m.Index') →
      plogFindConflict ls.prev es ents = W64 0 ∨
      uint.Z ls.committed < uint.Z (plogFindConflict ls.prev es ents)) ∧
     m.From' ≠ id ∧
     s.role ≠ .leader) →
  (m.Type' = MsgHeartbeat →
     uint.Z m.Commit' ≤ plogLastIndexZ s.logst.prev (s.logst.sents ++ s.logst.uents) ∧
     m.From' ≠ id) →
  (m.Type' = MsgTransferLeader ∨ m.Type' = MsgTimeoutNow →
     (m.Type' = MsgTransferLeader → (s.lead = W64 0 ∨ (m.Term' = W64 0 ∧ s.lead ≠ id)) ∧
        ents = [] ∧ cl = [] ∧
        (s.lead ≠ W64 0 → (s.gh.xw !! (s.lead, s.term)).isSome)) ∧
     (m.Type' = MsgTimeoutNow → uint.Z s.term + 1 < 2 ^ 64 ∧ NStateWf s ∧
       uint.Z s.logst.fl ≤ uint.Z s.logst.applied)) →
  (m.Type' = MsgSnap →
     sn = some sv ∧ scfg = sv.Metadata'.ConfState'.lists ∧
     SnapScopeIf id sv scfg ∧ s.role = .follower ∧ s.votes = ∅ ∧ m.From' ≠ id ∧
     s.gh.ns = false) →
  (m.Type' = MsgProp ∨ m.Type' = MsgReadIndex ∨ m.Type' = MsgTransferLeader → rs = []) →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgIn ml (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard)
               ⟨m, ents, sn, cl, rs⟩ ∗
      "#Hcert" ∷ rcvSrc s.gh.sn m.Type' sn }}
    (App (App (Val #(functions stepFollower [])) (Val #r)) (Val #ml))
  {{ (err : GoInterface) (s' : NState) (dropped : Bool) (c' : CfgM), RET #err;
      ownRaftPhysCV c' c'.voters r id s' ∗
      ⌜FollowerStepResultC c scfg id s m ents sv dropped s' c' cl⌝ ∗
      (if dropped then globalAddr ErrProposalDropped ↦□ err
       else ⌜err = interface.nil⌝) }}

/-- `stepFollower.spec`'s untraced instance: every gate from the struct's nil logger, `G := emp`. -/
theorem stepFollower.untraced (h : stepFollower.spec (GF := GF) (hG := hG)) :
    stepFollower.untracedTriple (GF := GF) (hG := hG) := by
  intro c scfg r id s ml m ents sn rs sv cl Hty Hri Hstz Hprop Happ Hhb Hrest Hsnap Hnors htr
  iintro %Φ ⟨#Hpkg, Hphys, Hm, #Hcert⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c scfg r id s ml m ents sn rs sv cl (fun _ => iprop(emp)) (fun _ => iprop(emp))
    Hty Hri Hstz Hprop Happ Hhb Hrest
    (fun hs => let ⟨a, b, c', d, e, f, g⟩ := Hsnap hs; ⟨a, b, c', d, e, f, g, htr⟩) Hnors
    (PermInv.const _) (IdxFree.const _ _) $$ [Hphys Hm]
  · dsimp only
    iframe Hpkg Hphys Hm Hcert
    rw [htr]
    isplitr
    · iempintro
    isplitr
    · iintro %_ %s1 %mm %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro %_ %_ %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro %_ -
      iapply hookGate_none r _ tl iprop(emp) Htlok
      iframe Htl
    · imodintro
      iintro %_ %pvs %y %_ %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
  inext
  iintro %err %s' %dropped %c' ⟨Hphys, %Hres, Herr, -⟩
  iapply HΦ $$ %err %s' %dropped %c'
  iframe Hphys Herr
  ipureintro; exact Hres

/-- `stepLeader.spec` at an untraced node (the statement before slice 8). -/
abbrev stepLeader.untracedTriple : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (k0 : Nat),
  (m.Type' = MsgVoteResp ∨ m.Type' = MsgBeat ∨
   m.Type' = MsgHeartbeatResp ∨ m.Type' = MsgAppResp ∨
   m.Type' = MsgProp ∨ m.Type' = MsgApp ∨
   m.Type' = MsgHeartbeat ∨ m.Type' = MsgPreVoteResp ∨
   m.Type' = MsgReadIndex ∨
   (m.Type' = MsgReadIndexResp ∨ m.Type' = MsgForgetLeader ∨ m.Type' = MsgTimeoutNow ∨
    m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus ∨ m.Type' = MsgTransferLeader ∨
    m.Type' = MsgCheckQuorum)) →
  s.role = .leader →
  (m.Type' = MsgBeat ∨ m.Type' = MsgTransferLeader → s.term ≠ W64 0) →
  (m.Type' = MsgAppResp → m.From' ≠ W64 0) →
  (m.Type' = MsgHeartbeatResp ∨ (m.Type' = MsgAppResp ∧ m.Reject' = true) →
   m.From' ≠ id) →
  (m.Type' = MsgProp →
   ents ≠ [] ∧
   (ents.length : Int) < 2^61 ∧
   s.term ≠ W64 0) →
  (m.Type' = MsgHeartbeatResp ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgReadIndex →
   RdOk c.voters s.rd ∧ s.term ≠ W64 0) →
  (m.Type' = MsgReadIndex → ents ≠ []) →
  (m.Type' = MsgHeartbeatResp →
   (ctx = [] ∨ 8 ≤ ctx.length) ∧
   (ctx ≠ [] → uint.Z (leToU64 (ctx.take 8))
                 ≤ uint.Z s.rd.ro.confirmed + (s.rd.ro.pending.length : Int)) ∧
   c.voters ≠ ∅) →
  (m.Type' = MsgAppResp →
    (m.Reject' = false → uint.Z m.Index' ≤ uint.Z (logLast s.logst)) ∧
    (m.Reject' = true → s.gh.ns = true →
      2 ≤ uint.Z m.Index' ∧ 1 ≤ uint.Z m.RejectHint' ∧ uint.Z m.RejectHint' ≤ uint.Z m.Index' ∧
      (∀ t0, plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) (W64 1) = some t0 →
        uint.Z t0 ≤ 1))) →
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgIn ml (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard)
               ⟨m, ents, sn, ctx, rs⟩ ∗
      "Hcc" ∷ (⌜m.Type' = MsgProp⌝ -∗ ∃ cs, ccEntsOk ents cs) ∗
      "#Hrc" ∷ ⧖ k0 }}
    (App (App (Val #(functions stepLeader [])) (Val #r)) (Val #ml))
  {{ (err : GoInterface) (s' : NState) (dropped : Bool), RET #err;
      ownRaftPhysCV c c.voters r id s' ∗
      (⌜m.Type' = MsgProp ∧ dropped = false⌝ -∗ ⧖ (k0 + ents.length)) ∗
      ⌜LeaderStepResultC c id s m ents dropped s' ctx⌝ ∗
      (if dropped then globalAddr ErrProposalDropped ↦□ err
       else ⌜err = interface.nil⌝) }}

/-- `stepLeader.spec`'s untraced instance: every gate from the struct's nil logger, `G := emp`. -/
theorem stepLeader.untraced (h : stepLeader.spec (GF := GF) (hG := hG)) :
    stepLeader.untracedTriple (GF := GF) (hG := hG) := by
  intro c r id s ml m ents sn ctx rs k0 Hty Hlead Htz Hfrom0 Hself Hprop Hrdnz Hri Hhr Hack htr
  iintro %Φ ⟨#Hpkg, Hphys, Hm, Hcc, #Hrc⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  iapply h c r id s ml m ents sn ctx rs k0 (fun _ => iprop(emp)) (fun _ => iprop(emp)) iprop(emp)
    (fun _ => iprop(emp)) (fun _ _ _ => iprop(emp))
    Hty Hlead Htz Hfrom0 Hself Hprop Hrdnz Hri Hhr Hack (fun _ h => absurd htr h)
    (IdxFree.const _ _) (IdxFree.const _ _) (fun _ _ => IdxFree.const _ _) $$ [Hphys Hm Hcc]
  · try dsimp only
    iframe Hpkg Hphys Hm Hcc Hrc
    rw [htr]
    isplitr
    · iempintro
    isplitr
    · imodintro
      iintro %_ %to %cm %o %_ %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro %_ %_ %mm %o %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · imodintro
      iintro %_ %_ %to %cm %o %_ %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro %_ %o -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro %_ %mm %o %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iapply trNoSnap_none
    isplitr
    · iintro %_ -
      iapply hookGate_none r _ tl iprop(emp) Htlok
      iframe Htl
    -- (slice 9) the three remaining arms' gates
    isplitr
    · iintro %_ %cs _ - -
      iapply hookGateN_none r _ _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro %_ %cs _ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · imodintro
      iintro %_ %cs %to %mm %o _ %_ %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro %_ %mm %o %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · imodintro
      iintro %_ %mm %o %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · iintro %_ %_ %pvs %b %N %_ %_ - -
      iapply hookGate_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · imodintro
      iintro %_ %N %mm %o %_ %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · imodintro
      iintro %_ %_ %N %k %to %cm %o %_ %_ %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    isplitr
    · imodintro
      iintro %_ %b %N %to %mm %o %_ %_ -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
    · imodintro
      iintro %_ %b %N %o -
      iapply hookGateOpt_none r _ tl iprop(emp) Htlok
      iframe Htl
  inext
  iintro %err %s' %dropped ⟨Hphys, Hrc', %Hres, Herr, -⟩
  iapply HΦ $$ %err %s' %dropped
  iframe Hphys Hrc' Herr
  ipureintro; exact Hres

end untraced

end EtcdGrove
end Perennial
