/-
**A replayed `AddNode`: `applyConfChange(cc, ep, false)`** (R2d'a A4, 2026-11-06; DRAFT, nothing
frozen: `notes/restart-plan.md`, "R2d' Scope (approved 2026-11-06)"). The proof of
`ApplyRDefs.lean`'s `EtcdServer.applyConfChange.specRep` from the translated body, over the callee
specs `EtcdServer__applyConfChange.lean`'s proof uses, at `shouldApplyV3 = false`. Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyRDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyConfChange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
  go_etcd_io.etcd.server.v3.etcdserver.cindex

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The steps `wp_auto` takes, one by one. -/
local macro "wsteps" : tactic => `(tactic| repeat (first | wp_pure | wp_load | wp_store | wp_alloc_auto))

set_option maxHeartbeats 4000000 in
/-- **`applyConfChange.specRep`** (R2d'a A4, DRAFT): the replayed `AddNode`, from the body. -/
theorem EtcdServer.applyConfChange.wp_proofRep
    (hLogger : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hValid : membership.RaftCluster.ValidateConfigurationChange.spec (GF := GF) (hG := hG))
    (hAdd : membership.RaftCluster.AddMember.spec (GF := GF) (hG := hG))
    (hSetCS : storage.BackendHooks.SetConfState.spec (GF := GF) (hG := hG))
    (hGetType : raftpb.ConfChange.GetType.spec (GF := GF) (hG := hG))
    (hGetNodeId : raftpb.ConfChange.GetNodeId.spec (GF := GF) (hG := hG))
    (hUnmarshal : encoding.json.Unmarshal.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyConfChange.specRep (GF := GF) (hG := hG) := by
  intro s cc ep m cs E γs γB cl rs be al st lp lg bh ix lgh tl lid prs lgc cid Hok HRO Hpeer Hsz
  obtain ⟨hty0, hin, hctx⟩ : m.type = W32 0 ∧ m.nodeId ∈ γs.raft.cfg ∧
      membership.ccContextOf m.context = some (m.nodeId, false) := ⟨Hok.1, Hok.2.1, Hok.2.2.1⟩
  wp_start as ⟨#Hlg, %Hlgnn, Hlr, #Hcl, #Hclg, %Hclgnn, #Hcid, Hcc, Hcs, #Hbh, #Hbhi, #Htr, #Hmid,
    Hmr, HRS⟩
  try wp_method_call
  try wp_call
  wp_auto
  wp_apply hLogger $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe; ipureintro; exact Hlgnn
  rw [HRO]
  iunfold srvRestOwnH at HRS
  iunfold srvRestOwn at HRS
  iunfold srvObjsOn at HRS
  iunfold clusterBeOn at HRS
  icases HRS with ⟨⟨Hcb, Hnc, Hcm, %Hmi⟩, Hal, Hau, Hle, %mbl, %lgm, %Hlgmnn, Hbef, #Hmbe, #Hmlg⟩
  ihave #Pmem : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Prpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Pjson : isPkgInit (PROP := IProp GF) pkg_id.encoding.json $$ []
  · iPkgInit
  ihave #Pstor : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  -- `ValidateConfigurationChange(cc, false)`: `nil`, no read
  wp_apply (hValid cl cc (DFrac.own 1) (DFrac.own 1) m false
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty, #mbl⟩
    iprop(True) (membership.membersOfBk rs.bk).1 (membership.membersOfBk rs.bk).2 (.inl hty0)
    (fun _ => ⟨_, hctx⟩))
    $$ [Hbef Hcc] as %err ⟨Hbef, Hcc, Herr⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]; iframe #; iframe
  try simp only [Bool.false_eq_true, ↓reduceIte]
  icases Herr with %Herr
  subst Herr
  wp_pures
  wp_auto
  imod ownConfChange_persist _ _ _ $$ Hcc with #Hcc
  iunfold epConfState at Hcs
  icases Hcs with ⟨Hcsf, #Hcsok⟩
  wsteps
  -- `s.beHooks.SetConfState(ep.confState)`, the conf state kept
  wp_apply (hSetCS bh ix lgh cs) $$ []
  · iframe #
    iunfold epCsOk at Hcsok
    icases Hcsok with (%h | ⟨%c, #Hc⟩)
    · ileft; ipureintro; exact h
    · iright; iexists c; iapply csPts_weaken; iexact Hc
  wp_apply (hGetType.1 cc _ m) $$ [] as -
  · iframe #
  rw [hty0, show decide ((W32 0 : w32) = W32 3) = false by simp]
  wsteps
  icases ownConfChange_context_acc' cc _ m $$ Hcc with ⟨%csl, HC, #Hcsl, Hcc'⟩
  wsteps
  irename «$r0» => Hcv
  wp_apply (hUnmarshal csl m.context DFrac.discard _ _ m.nodeId false hctx) $$ [Hcv]
    as %err ⟨%Herr, -, %v', %pus, Hcv, Hpus, Hcus, %Hv'⟩
  · iframe #; iframe
  subst Herr
  obtain ⟨Hvid, Hvprom, Hpus, Hvlrn, Hvnm⟩ := Hv'
  ihave #Hcc := Hcc' $$ HC
  wsteps
  iStructNamed Hcv
  ihave %Hmnn := typedPointsto_not_null _ _ _ $$ Member
  iStructNamed Member
  iStructNamed RaftAttributes
  iStructNamed Attributes
  wp_apply (hGetNodeId.1 cc _ m) $$ [] as -
  · iframe #
  rw [Hvid]
  simp only [_root_.decide_true, Bool.not_true]
  wsteps
  rw [Hvprom]
  wsteps
  rw [Hvlrn, Hvnm]
  subst Hpus
  imod membership.memberAt_of_owned («$r0_ptr».[go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext, go!"Member"]) 1 (membership.ccMemberAt m) _ _ Hmnn $$ [ID PeerURLs IsLearner Name ClientURLs Hpus Hcus] with Hm
  · simp only [membership.ccMemberAt]
    iframe
  simp only [ccMembRes]
  icases Hmr with ⟨#Hrc, %γn, %c, %ps, %Hcl', Hlive, #Hmd, %Hdk⟩
  ihave #HrcG := (membership.isRaftCluster_static cl).1 $$ Hrc
  -- `AddMember(&ctx.Member, false)`: only a log line, under the cluster's lock
  wp_apply (hAdd cl membership.rcStatic rs.mem _ (DFrac.own 1) (membership.ccMemberAt m) false lgc
    cid ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty, #mbl⟩
    iprop(True) iprop(True) (rcStatic_insert _ _) Hsz) $$ [Hcm Hm Hbef]
    as ⟨Hbef, Hpost⟩
  · iframe #; iframe
    isplitr
    · ipureintro; exact Hclgnn
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  try simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hpost with ⟨Hcm, Hmh⟩
  iunfold membership.memberAt at Hmh
  icases Hmh with ⟨%Hmhnn, %pu, %cu, ID, PeerURLs, IsLearner, Name, ClientURLs, Hpus, Hcus⟩
  wsteps
  wp_apply (hMID s lid) $$ []
  · iframe #
  -- the conclusion, after `AddPeer` or not
  by_cases hlid : m.nodeId = lid
  · wsteps
    rw [decide_eq_true hlid]
    simp only [Bool.not_true]
    wsteps
    iapply HΦ
    isplitr
    · ipureintro; rfl
    iframe Hlr
    isplitr
    · iexists m; iframe Hcc; ipureintro; rfl
    isplitl [Hcsf]
    · iunfold epConfState; iframe Hcsf Hcsok
    isplitl [Hlive]
    · iframe Hrc; iexists γn, c, ps; iframe Hlive Hmd; ipureintro; exact ⟨Hcl', Hdk⟩
    iunfold srvRestOwnH; iunfold srvRestOwn; iunfold srvObjsOn; iunfold clusterBeOn
    iframe Hcb Hnc Hcm Hal Hau Hle
    isplitr
    · ipureintro; exact Hmi
    iexists mbl, lgm
    iframe Hbef Hmbe Hmlg
    ipureintro; exact Hlgmnn
  · wsteps
    rw [decide_eq_false hlid]
    simp only [Bool.not_false]
    ihave #Ptr : isPkgInit (PROP := IProp GF)
        pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp $$ []
    · iPkgInit
    wsteps
    wp_apply (rafthttp.Transport.AddPeer_known γn tl c prs m.nodeId _ (Hpeer hlid))
      $$ [Hlive] as Hlive
    · iframe #; iframe
    wsteps
    iapply HΦ
    isplitr
    · ipureintro; rfl
    iframe Hlr
    isplitr
    · iexists m; iframe Hcc; ipureintro; rfl
    isplitl [Hcsf]
    · iunfold epConfState; iframe Hcsf Hcsok
    isplitl [Hlive]
    · iframe Hrc; iexists γn, c, ps; iframe Hlive Hmd; ipureintro; exact ⟨Hcl', Hdk⟩
    iunfold srvRestOwnH; iunfold srvRestOwn; iunfold srvObjsOn; iunfold clusterBeOn
    iframe Hcb Hnc Hcm Hal Hau Hle
    isplitr
    · ipureintro; exact Hmi
    iexists mbl, lgm
    iframe Hbef Hmbe Hmlg
    ipureintro; exact Hlgmnn

end proof

end EtcdGrove
end Perennial
