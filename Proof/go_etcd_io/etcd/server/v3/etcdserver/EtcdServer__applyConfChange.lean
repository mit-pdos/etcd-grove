/-
Proof of `Spec/.../EtcdServer__applyConfChange.lean` (D43 M5e, 2026-10-26; until then an axiom).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyConfChange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ValidateConfigurationChange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__AddMember
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__RemoveMember
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.membershipBackend__MustSaveMemberToBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.membershipBackend__MustDeleteMemberFromBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.membershipBackend__MustReadMembersFromBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.BackendHooks__SetConfState
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__ConsistentApplyingIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__RemovePeer
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__GetNodeId
public import Spec.encoding.json.Unmarshal
public import Spec.go_uber_org.zap.Logger__Error
public import Spec.go_uber_org.zap.Bool
public import Spec.go_uber_org.zap.Error
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportFull

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

/-- A conf change's `Context` field, borrowed (as `ValidateConfigurationChange`'s proof's). -/
theorem ownConfChange_context_acc' (p : Loc) (dq : DFrac) (m : ConfChangeM) :
    ownConfChange (GF := GF) p dq m ⊢ ∃ cs : GoSlice,
      p.[raftpb.ConfChange, go!"Context"] ↦{dq} cs ∗ cs ↦*□ m.context ∗
      (p.[raftpb.ConfChange, go!"Context"] ↦{dq} cs -∗ ownConfChange p dq m) := by
  unfold ownConfChange
  iintro H
  iNamed H
  iexists cs
  iframe HC Hcs
  iintro HC
  iexists pt, pn, pi, cs, uf
  simp only [named]
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe #

/-- An insert keeps the static side condition (the local member still in the map). -/
theorem rcStatic_insert (k : w64) (l : Loc) :
    ∀ lid ms rm, membership.rcStatic (GF := GF) lid ms rm ⊢
      membership.rcStatic lid (GMap.insert k l ms) rm := by
  intro lid ms rm
  unfold membership.rcStatic
  iintro %h
  ipureintro
  refine ⟨?_, h.2⟩
  by_cases hk : k = lid
  · subst hk; rw [GMap.lookup_insert]; simp
  · rw [GMap.lookup_insert_ne _ _ hk]; exact h.1

/-- An insert keeps the dynamic side condition (it says nothing of the map). -/
theorem rcDyn_insert (γ : GName) (k : w64) (l : Loc) :
    ∀ lid ms rm, membership.rcDyn (GF := GF) γ lid ms rm ⊢
      membership.rcDyn γ lid (GMap.insert k l ms) rm := fun _ _ _ => .rfl

set_option hygiene false in
/-- The return of the `v3 = false` branch (raft's static mode, an `AddNode`): nothing written. -/
local macro "nov3_post" : tactic => `(tactic| (
  (try wp_auto)
  have hcr : ccRest false m rs = rs := by simp [ccRest]
  have hpa : ccPeersAfter false m rs.bk prs = prs := by
    unfold ccPeersAfter; rw [ite_eq_right (by rw [hty0]; simp)]
  have hdvn : dv = none := by
    cases hdv : dv with
    | none => rfl
    | some γn => exact absurd (Hdyn γn hdv).1 (by simp)
  subst hdvn
  rw [hcr, hpa]
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iframe Hlr Hua
  isplitl [Hcsf]
  · iexists m, cs
    iframe Hcc
    isplitr
    · ipureintro; rfl
    iunfold epConfState
    iframe Hcsf Hcsok
  isplitl [Hrb Hcm Hal Hau Hle Hbef]
  · iunfold srvRestOwnH; iunfold srvRestOwn; iunfold srvObjsOn; iunfold clusterBeOn
    iframe Hrb Hcm Hal Hau Hle
    iexists mbl, lgm
    iframe Hbef Hmbe Hmlg
    ipureintro; exact Hlgmnn
  simp only [Bool.false_eq_true, ↓reduceIte, dvCCPost, ccMembRes, hst]
  iframe Hpre Hrt Hrc
  iexists γn, c
  iframe Hfz Htk
  ipureintro; exact Hcl))

/-- A conf change's `NodeId` field, replaced (`cc.NodeId = new(raft.None)`). -/
theorem ownConfChange_nodeId_acc (p : Loc) (m : ConfChangeM) :
    ownConfChange (GF := GF) p (DFrac.own 1) m ⊢ ∃ pn : Loc,
      p.[raftpb.ConfChange, go!"NodeId"] ↦ pn ∗
      (∀ (pn' : Loc) (v : w64), p.[raftpb.ConfChange, go!"NodeId"] ↦ pn' -∗ cellRO pn' v -∗
        ownConfChange p (DFrac.own 1) { m with nodeId := v }) := by
  unfold ownConfChange
  iintro H
  iNamed H
  iexists pn
  iframe HN
  iintro %pn' %v HN #cN'
  iexists pt, pn', pi, cs, uf
  simp only [named]
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe #

set_option hygiene false in
/-- `s.r.ApplyConfChange(cc)` of the change `cm` (`cc` read-only at it): raft's static clause
without a view (`hraft` its `ccRaftOk`), the dynamic contract with one (`hdynp` its
`DynCCPreOp`); the answer `csp` (`Hcsp`) and the view after (`Hdvq`). -/
local macro "raft_cc " cm:term:max " with " hraft:term:max hdynp:term:max " then " k:tactic : tactic => `(tactic| (
  rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"ApplyConfChange")]
  wp_pures
  rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"ApplyConfChange")]
  wp_pures
  cases hdvc : dv with
  | none =>
    ihave #Hrn' := Hrn
    iunfold srvRaftNode at Hrn'
    icases Hrn' with ⟨%nd, #Hnd, #Hprop⟩
    iunfold raftPropose at Hprop
    icases Hprop with ⟨%ni, %Hni, -, -, -, #HACC⟩
    wp_load
    rw [Hni]
    wp_pures
    wp_apply HACC $$ %(interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #cc) %$cm
        %(($hraft hdvc).1) %(($hraft hdvc).2) []
      as %csp Hcsp
    · simp only [ownConfChangeI]; iexists cc; iframe Hcc; ipureintro; rfl
    ihave Hdvq : dvCCPost (GF := GF) none k cs' $$ []
    · iunfold dvCCPost; itrivial
    clear hdvc $hraft $hdynp Hdv Hdyn
    $k
  | some γn =>
    iunfold dvCCPre at Hdvp
    icases Hdvp with ⟨#Hrnd, Hnc, #Hdl⟩
    iunfold srvRaftNodeDyn at Hrnd
    icases Hrnd with ⟨%nd, #Hnd, #Hdcc⟩
    iunfold raftApplyCCDyn at Hdcc
    icases Hdcc with ⟨%ni, %Hni, -, #HACC⟩
    wp_load
    rw [Hni]
    wp_pures
    wp_apply HACC $$ %(interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #cc) %$cm %ds %ca
        %cfg %k %e %cs' %($hdynp γn hdvc) [Hnc]
      as %csp ⟨Hcsp, Hdvq⟩
    · iframe Hnc Hdl; simp only [ownConfChangeI]; iexists cc; iframe Hcc; ipureintro; rfl
    ihave Hdvq : dvCCPost (GF := GF) (some γn) k cs' $$ [Hdvq]
    · iunfold dvCCPost; iexact Hdvq
    clear hdvc $hraft $hdynp Hdv Hdyn
    $k))

/-- The steps `wp_auto` takes, one by one (in some contexts `wp_auto` reports no progress). -/
local macro "wsteps" : tactic => `(tactic| repeat (first | wp_pure | wp_load | wp_store | wp_alloc_auto))

set_option hygiene false in
/-- A failed validation, after raft's no-op: the consistent index stored, the error returned. -/
local macro "fail_tail" : tactic => `(tactic| (
  ihave #Pci : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  wsteps
  icases Hlens $$ Hpre with ⟨Hap, Hpre'⟩
  wp_apply (hCAI ci i t) $$ [Hap] as Hap
  · iframe #; iframe
  ihave Hpre := Hpre' $$ Hap
  wsteps
  ihave Hwp := Hsci $$ Hpre
  rw [method_unfold (t := go.GoType.PointerType consistentIndex.ty) (m := go!"SetConsistentIndex")]
  wp_apply_core wp_wand $$ Hwp
  iintro %_v ⟨%Hv, Hadv⟩
  subst Hv
  wp_auto
  have hcr : ccRest true m rs = rs := by
    unfold ccRest; rw [ite_eq_right (fun h => hv h.2)]
  have hpa : ccPeersAfter true m rs.bk prs = prs := by
    unfold ccPeersAfter
    refine ite_eq_right (fun h => ?_)
    rcases h.2 with h2 | h2
    · cases h2
    · exact absurd h2 hv
  rw [hcr, hpa]
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iframe Hlr Hua Hdvq Hmr Hrt
  isplitl [Hcs]
  · iexists { m with nodeId := W64 0 }, cs
    iframe Hcc Hcs
    ipureintro; rfl
  try simp only [↓reduceIte]
  isplitl [Hrb Hcm Hal Hau Hle Hbef]
  · iunfold srvRestOwnH; iunfold srvRestOwn; iunfold srvObjsOn; iunfold clusterBeOn
    iframe Hrb Hcm Hal Hau Hle
    iexists mbl, lgm
    iframe Hbef Hmbe Hmlg
    ipureintro; exact Hlgmnn
  iright
  iexact Hadv))

set_option hygiene false in
/-- A passed validation, after raft's change: `ep.confState`, the backend hooks' conf state, the
change's type. -/
local macro "succ_tail" : tactic => `(tactic| (
  wsteps
  icases Hcsp with ⟨%csm, Hcsp⟩
  imod csPts_persist _ _ _ _ $$ Hcsp with #Hcsp
  ihave #Hcsok : ownCSM (GF := GF) csp DFrac.discard csm $$ []
  · iapply csPts_weaken; iexact Hcsp
  wp_apply (hSetCS bh ix lgh csp) $$ []
  · iframe #; first | done | (iright; iexists csm; iexact Hcsok)
  wp_apply (hGetType.1 cc _ m) $$ [] as -
  · iframe #
  rcases Hty with hty0 | hty1
  · rw [hty0, show decide ((W32 0 : w32) = W32 3) = false by simp]
    have hctx : membership.ccContextOf m.context = some (m.nodeId, false) := by
      rcases Hok with ⟨-, -, h⟩ | ⟨-, h1, -⟩
      · exact h
      · rw [hty0] at h1; exact absurd h1 (by simp)
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
    ihave Hm : membership.memberAt («$r0_ptr».[go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext, go!"Member"]) 1 (membership.ccMemberAt m) $$ [ID PeerURLs IsLearner Name ClientURLs Hpus Hcus]
    · iunfold membership.memberAt
      isplitr
      · ipureintro; exact Hmnn
      iexists _, _
      simp only [membership.ccMemberAt]
      iframe
    ihave #HbeSave : membership.beSaveOk
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty, #mbl⟩
        («$r0_ptr».[go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext, go!"Member"]) (membership.ccMemberAt m)
        iprop(Pre ∗ (Q ={⊤}=∗ E.P ∗ Post) ∗ mvcc.storeWT E.γ ∗ mvcc.storeRT E.γ ∗
          backend.rbOwn d.γB rs.bk)
        iprop(Post ∗ mvcc.storeRT E.γ ∗ backend.rbOwn d.γB (apply.bkPut rs.bk go!"members"
          (apply.memberKey m.nodeId) (apply.memberEnc (membership.ccMemberAt m)))) $$ []
    · iunfold membership.beSaveOk
      iintro !> %Φ' !> ⟨⟨Hp, Hu, Hw, Ht, Hb⟩, Hmm⟩ HΦ'
      wp_apply (hSave mbl lgm E.γ d E.P E.f Pre Q Post rs.bk («$r0_ptr».[go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext, go!"Member"]) (membership.ccMemberAt m) Hkb Hmem)
        $$ [Hp Hu Hw Ht Hb Hmm] as ⟨Hpo, Ht, Hb, Hmm⟩
      · iframe #; iframe
        isplitr
        · ipureintro; exact Hlgmnn
        iunfold mvcc.csContract
        iframe Hp Hu
        iexact Hhook
      iapply HΦ'
      iframe
    cases hrd : γs.raft.reDyn with
    | none =>
      simp only [ccMembRes, hrd]
      icases Hmr with ⟨#Hrc, %γn, %c, %Hcl, #Hfz, Htk⟩
      ihave #HrcG := (membership.isRaftCluster_static cl).1 $$ Hrc
      wp_apply (hAdd cl membership.rcStatic rs.mem _ (DFrac.own 1) (membership.ccMemberAt m) true lgc cid
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty, #mbl⟩
        iprop(Pre ∗ (Q ={⊤}=∗ E.P ∗ Post) ∗ mvcc.storeWT E.γ ∗ mvcc.storeRT E.γ ∗
          backend.rbOwn d.γB rs.bk)
        iprop(Post ∗ mvcc.storeRT E.γ ∗ backend.rbOwn d.γB (apply.bkPut rs.bk go!"members"
          (apply.memberKey m.nodeId) (apply.memberEnc (membership.ccMemberAt m)))) (rcStatic_insert _ _) (Hsz hty0)) $$ [Hcm Hm Hbef Hpre Hupd Hwt Hrt Hrb]
        as ⟨Hbef, Hpost⟩
      · iframe #; iframe
        isplitr
        · ipureintro; exact Hclgnn
        try simp only [↓reduceIte]
        iframe #
        iframe
      try simp only [↓reduceIte]
      icases Hpost with ⟨⟨Hpo, Hrt, Hrb⟩, Hcm⟩
      icases membership.clusterMemIn_acc cl _ _ _ $$ Hcm with ⟨Hmh, Hcmb⟩
      ihave Hmh : membership.memberAt («$r0_ptr».[go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext, go!"Member"]) (1 : Qp).half (membership.ccMemberAt m) $$ [Hmh]
      · iExactEq Hmh
        rw [GMap.lookup_insert]; rfl
      iunfold membership.memberAt at Hmh
      icases Hmh with ⟨%Hmhnn, %pu, %cu, ID, PeerURLs, IsLearner, Name, ClientURLs, Hpus, Hcus⟩
      wsteps
      wp_apply (hMID s lid) $$ []
      · iframe #
      have hidm : (membership.ccMemberAt m).id = m.nodeId := rfl
      by_cases hlid : m.nodeId = lid
      · wsteps
        rw [decide_eq_true hlid]
        simp only [Bool.not_true]
        wsteps
        ihave Hmh : membership.memberAt («$r0_ptr».[go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext, go!"Member"]) (1 : Qp).half (membership.ccMemberAt m) $$ [ID PeerURLs IsLearner Name ClientURLs Hpus Hcus]
        · iunfold membership.memberAt
          isplitr
          · ipureintro; exact Hmhnn
          iexists _, _
          simp only [membership.ccMemberAt]
          iframe
        ihave Hcm := Hcmb $$ [Hmh]
        · iExactEq Hmh
          rw [GMap.lookup_insert]; rfl
        ihave Hcm := membership.clusterMemIn_mem cl _ _ _ $$ Hcm
        try rw [hidm] at *
        have hcr : ccRest true m rs = ⟨apply.bkPut rs.bk go!"members" (apply.memberKey m.nodeId)
            (apply.memberEnc (membership.ccMemberAt m)), rs.mem.insert m.nodeId (membership.ccMemberAt m)⟩ := by
          unfold ccRest; rw [ite_eq_left ⟨rfl, hv⟩, ite_eq_left hty0]; rfl
        have hpa : ccPeersAfter true m rs.bk prs = prs := by
          unfold ccPeersAfter
          refine ite_eq_right (fun h => ?_)
          rw [hty0] at h; exact absurd h.1 (by simp)
        rw [hcr, hpa]
        iapply HΦ
        isplitr
        · ipureintro; rfl
        iframe Hlr Hua Hdvq Hrt
        isplitl [Hcsf]
        · iexists m, csp
          iframe Hcc
          isplitr
          · ipureintro; rfl
          iunfold epConfState
          iframe Hcsf
          iunfold epCsOk; iright; iexists csm; iexact Hcsok
        isplitl [Hrb Hcm Hal Hau Hle Hbef]
        · iunfold srvRestOwnH; iunfold srvRestOwn; iunfold srvObjsOn; iunfold clusterBeOn
          iframe Hal Hau Hle
          isplitl [Hrb Hcm]
          · simp only [apply.RestM.putIn_bk]
            iframe Hrb
            iexact Hcm
          iexists mbl, lgm
          iframe Hbef Hmbe Hmlg
          ipureintro; exact Hlgmnn
        try simp only [↓reduceIte]
        isplitl [Hpo]
        · ileft; iexact Hpo
        try simp only [ccMembRes, hrd]
        iframe Hrc
        iexists γn, c
        iframe Hfz Htk
        ipureintro; exact Hcl
      · wsteps
        rw [decide_eq_false hlid]
        simp only [Bool.not_false]
        ihave #Ptr : isPkgInit (PROP := IProp GF)
            pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp $$ []
        · iPkgInit
        wsteps
        wp_apply (rafthttp.Transport.AddPeer_frozen γn tl c prs m.nodeId pu (Hpeer hty0 hlid))
          $$ [Htk] as Htk
        · iframe #; iframe
        wsteps
        ihave Hmh : membership.memberAt («$r0_ptr».[go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext, go!"Member"]) (1 : Qp).half (membership.ccMemberAt m) $$ [ID PeerURLs IsLearner Name ClientURLs Hpus Hcus]
        · iunfold membership.memberAt
          isplitr
          · ipureintro; exact Hmhnn
          iexists _, _
          simp only [membership.ccMemberAt]
          iframe
        ihave Hcm := Hcmb $$ [Hmh]
        · iExactEq Hmh
          rw [GMap.lookup_insert]; rfl
        ihave Hcm := membership.clusterMemIn_mem cl _ _ _ $$ Hcm
        try rw [hidm] at *
        have hcr : ccRest true m rs = ⟨apply.bkPut rs.bk go!"members" (apply.memberKey m.nodeId)
            (apply.memberEnc (membership.ccMemberAt m)), rs.mem.insert m.nodeId (membership.ccMemberAt m)⟩ := by
          unfold ccRest; rw [ite_eq_left ⟨rfl, hv⟩, ite_eq_left hty0]; rfl
        have hpa : ccPeersAfter true m rs.bk prs = prs := by
          unfold ccPeersAfter
          refine ite_eq_right (fun h => ?_)
          rw [hty0] at h; exact absurd h.1 (by simp)
        rw [hcr, hpa]
        iapply HΦ
        isplitr
        · ipureintro; rfl
        iframe Hlr Hua Hdvq Hrt
        isplitl [Hcsf]
        · iexists m, csp
          iframe Hcc
          isplitr
          · ipureintro; rfl
          iunfold epConfState
          iframe Hcsf
          iunfold epCsOk; iright; iexists csm; iexact Hcsok
        isplitl [Hrb Hcm Hal Hau Hle Hbef]
        · iunfold srvRestOwnH; iunfold srvRestOwn; iunfold srvObjsOn; iunfold clusterBeOn
          iframe Hal Hau Hle
          isplitl [Hrb Hcm]
          · simp only [apply.RestM.putIn_bk]
            iframe Hrb
            iexact Hcm
          iexists mbl, lgm
          iframe Hbef Hmbe Hmlg
          ipureintro; exact Hlgmnn
        try simp only [↓reduceIte]
        isplitl [Hpo]
        · ileft; iexact Hpo
        try simp only [ccMembRes, hrd]
        iframe Hrc
        iexists γn, c
        iframe Hfz Htk
        ipureintro; exact Hcl
    | some dynf =>
      simp only [ccMembRes, hrd]
      icases Hmr with ⟨%γn, %c, %γc, %rm, %Hcl, Hlive, #HrcG, Hrmo⟩
      wp_apply (hAdd cl (membership.rcDyn γc) rs.mem _ (DFrac.own 1) (membership.ccMemberAt m) true lgc cid
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty, #mbl⟩
        iprop(Pre ∗ (Q ={⊤}=∗ E.P ∗ Post) ∗ mvcc.storeWT E.γ ∗ mvcc.storeRT E.γ ∗
          backend.rbOwn d.γB rs.bk)
        iprop(Post ∗ mvcc.storeRT E.γ ∗ backend.rbOwn d.γB (apply.bkPut rs.bk go!"members"
          (apply.memberKey m.nodeId) (apply.memberEnc (membership.ccMemberAt m)))) (rcDyn_insert γc _ _) (Hsz hty0)) $$ [Hcm Hm Hbef Hpre Hupd Hwt Hrt Hrb]
        as ⟨Hbef, Hpost⟩
      · iframe #; iframe
        isplitr
        · ipureintro; exact Hclgnn
        try simp only [↓reduceIte]
        iframe #
        iframe
      try simp only [↓reduceIte]
      icases Hpost with ⟨⟨Hpo, Hrt, Hrb⟩, Hcm⟩
      icases membership.clusterMemIn_acc cl _ _ _ $$ Hcm with ⟨Hmh, Hcmb⟩
      ihave Hmh : membership.memberAt («$r0_ptr».[go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext, go!"Member"]) (1 : Qp).half (membership.ccMemberAt m) $$ [Hmh]
      · iExactEq Hmh
        rw [GMap.lookup_insert]; rfl
      iunfold membership.memberAt at Hmh
      icases Hmh with ⟨%Hmhnn, %pu, %cu, ID, PeerURLs, IsLearner, Name, ClientURLs, Hpus, Hcus⟩
      wsteps
      wp_apply (hMID s lid) $$ []
      · iframe #
      have hidm : (membership.ccMemberAt m).id = m.nodeId := rfl
      by_cases hlid : m.nodeId = lid
      · wsteps
        rw [decide_eq_true hlid]
        simp only [Bool.not_true]
        wsteps
        ihave Hmh : membership.memberAt («$r0_ptr».[go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext, go!"Member"]) (1 : Qp).half (membership.ccMemberAt m) $$ [ID PeerURLs IsLearner Name ClientURLs Hpus Hcus]
        · iunfold membership.memberAt
          isplitr
          · ipureintro; exact Hmhnn
          iexists _, _
          simp only [membership.ccMemberAt]
          iframe
        ihave Hcm := Hcmb $$ [Hmh]
        · iExactEq Hmh
          rw [GMap.lookup_insert]; rfl
        ihave Hcm := membership.clusterMemIn_mem cl _ _ _ $$ Hcm
        try rw [hidm] at *
        have hcr : ccRest true m rs = ⟨apply.bkPut rs.bk go!"members" (apply.memberKey m.nodeId)
            (apply.memberEnc (membership.ccMemberAt m)), rs.mem.insert m.nodeId (membership.ccMemberAt m)⟩ := by
          unfold ccRest; rw [ite_eq_left ⟨rfl, hv⟩, ite_eq_left hty0]; rfl
        have hpa : ccPeersAfter true m rs.bk prs = prs := by
          unfold ccPeersAfter
          refine ite_eq_right (fun h => ?_)
          rw [hty0] at h; exact absurd h.1 (by simp)
        rw [hcr, hpa]
        iapply HΦ
        isplitr
        · ipureintro; rfl
        iframe Hlr Hua Hdvq Hrt
        isplitl [Hcsf]
        · iexists m, csp
          iframe Hcc
          isplitr
          · ipureintro; rfl
          iunfold epConfState
          iframe Hcsf
          iunfold epCsOk; iright; iexists csm; iexact Hcsok
        isplitl [Hrb Hcm Hal Hau Hle Hbef]
        · iunfold srvRestOwnH; iunfold srvRestOwn; iunfold srvObjsOn; iunfold clusterBeOn
          iframe Hal Hau Hle
          isplitl [Hrb Hcm]
          · simp only [apply.RestM.putIn_bk]
            iframe Hrb
            iexact Hcm
          iexists mbl, lgm
          iframe Hbef Hmbe Hmlg
          ipureintro; exact Hlgmnn
        try simp only [↓reduceIte]
        isplitl [Hpo]
        · ileft; iexact Hpo
        try simp only [ccMembRes, hrd]
        iexists γn, c, γc, rm
        iframe Hlive HrcG Hrmo
        ipureintro; exact Hcl
      · wsteps
        rw [decide_eq_false hlid]
        simp only [Bool.not_false]
        ihave #Ptr : isPkgInit (PROP := IProp GF)
            pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp $$ []
        · iPkgInit
        wsteps
        wp_apply (rafthttp.Transport.AddPeer_known γn tl c prs m.nodeId pu (Hpeer hty0 hlid))
          $$ [Hlive] as Hlive
        · iframe #; iframe
        wsteps
        ihave Hmh : membership.memberAt («$r0_ptr».[go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext, go!"Member"]) (1 : Qp).half (membership.ccMemberAt m) $$ [ID PeerURLs IsLearner Name ClientURLs Hpus Hcus]
        · iunfold membership.memberAt
          isplitr
          · ipureintro; exact Hmhnn
          iexists _, _
          simp only [membership.ccMemberAt]
          iframe
        ihave Hcm := Hcmb $$ [Hmh]
        · iExactEq Hmh
          rw [GMap.lookup_insert]; rfl
        ihave Hcm := membership.clusterMemIn_mem cl _ _ _ $$ Hcm
        try rw [hidm] at *
        have hcr : ccRest true m rs = ⟨apply.bkPut rs.bk go!"members" (apply.memberKey m.nodeId)
            (apply.memberEnc (membership.ccMemberAt m)), rs.mem.insert m.nodeId (membership.ccMemberAt m)⟩ := by
          unfold ccRest; rw [ite_eq_left ⟨rfl, hv⟩, ite_eq_left hty0]; rfl
        have hpa : ccPeersAfter true m rs.bk prs = prs := by
          unfold ccPeersAfter
          refine ite_eq_right (fun h => ?_)
          rw [hty0] at h; exact absurd h.1 (by simp)
        rw [hcr, hpa]
        iapply HΦ
        isplitr
        · ipureintro; rfl
        iframe Hlr Hua Hdvq Hrt
        isplitl [Hcsf]
        · iexists m, csp
          iframe Hcc
          isplitr
          · ipureintro; rfl
          iunfold epConfState
          iframe Hcsf
          iunfold epCsOk; iright; iexists csm; iexact Hcsok
        isplitl [Hrb Hcm Hal Hau Hle Hbef]
        · iunfold srvRestOwnH; iunfold srvRestOwn; iunfold srvObjsOn; iunfold clusterBeOn
          iframe Hal Hau Hle
          isplitl [Hrb Hcm]
          · simp only [apply.RestM.putIn_bk]
            iframe Hrb
            iexact Hcm
          iexists mbl, lgm
          iframe Hbef Hmbe Hmlg
          ipureintro; exact Hlgmnn
        try simp only [↓reduceIte]
        isplitl [Hpo]
        · ileft; iexact Hpo
        try simp only [ccMembRes, hrd]
        iexists γn, c, γc, rm
        iframe Hlive HrcG Hrmo
        ipureintro; exact Hcl
  · -- `RemoveNode` (raft's dynamic mode only, `ccApplyOkM`)
    obtain ⟨hdynm, hin1⟩ : γs.raft.reDyn.isSome = true ∧ m.nodeId ∈ γs.raft.reCfg := by
      rcases Hok with ⟨h0, -⟩ | ⟨h, -, hin⟩
      · rw [hty1] at h0; exact absurd h0 (by simp)
      · exact ⟨h, hin⟩
    rw [hty1, show decide ((W32 1 : w32) = W32 3) = false by simp]
    wsteps
    wp_apply (hGetNodeId.1 cc _ m) $$ [] as -
    · iframe #
    wsteps
    cases hrd : γs.raft.reDyn with
    | none => rw [hrd] at hdynm; cases hdynm
    | some dynf =>
    simp only [ccMembRes, hrd]
    icases Hmr with ⟨%γn, %c, %γc, %rm, %Hcl, Hlive, #HrcG, Hrmo⟩
    ihave #HbeDel : membership.beDeleteOk
        ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty, #mbl⟩
        m.nodeId
        iprop(Pre ∗ (Q ={⊤}=∗ E.P ∗ Post) ∗ mvcc.storeWT E.γ ∗ mvcc.storeRT E.γ ∗
          backend.rbOwn d.γB rs.bk)
        iprop(Post ∗ mvcc.storeRT E.γ ∗ backend.rbOwn d.γB (apply.bkPut (apply.bkDel rs.bk
          go!"members" (apply.memberKey m.nodeId)) go!"members_removed" (apply.memberKey m.nodeId)
          membership.removedVal)) $$ []
    · iunfold membership.beDeleteOk
      iintro !> %Φ' !> ⟨Hp, Hu, Hw, Ht, Hb⟩ HΦ'
      wp_apply (hDelete mbl lgm E.γ d E.P E.f Pre Q Post rs.bk m.nodeId Hkb Hmem Hrem)
        $$ [Hp Hu Hw Ht Hb] as ⟨Hpo, Ht, Hb⟩
      · iframe #; iframe
        isplitr
        · ipureintro; exact Hlgmnn
        iunfold mvcc.csContract
        iframe Hp Hu
        iexact Hhook
      iapply HΦ'
      iframe
    wp_apply (hRemove cl γc rm rs.mem m.nodeId (DFrac.own 1) true lgc cid
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty, #mbl⟩
      iprop(Pre ∗ (Q ={⊤}=∗ E.P ∗ Post) ∗ mvcc.storeWT E.γ ∗ mvcc.storeRT E.γ ∗
          backend.rbOwn d.γB rs.bk)
      iprop(Post ∗ mvcc.storeRT E.γ ∗ backend.rbOwn d.γB (apply.bkPut (apply.bkDel rs.bk
          go!"members" (apply.memberKey m.nodeId)) go!"members_removed" (apply.memberKey m.nodeId)
          membership.removedVal))) $$ [Hrmo Hcm Hbef Hpre Hupd Hwt Hrt Hrb]
      as ⟨Hbef, Hpost⟩
    · iframe #; iframe
      isplitr
      · ipureintro; exact Hclgnn
      try simp only [↓reduceIte]
      iframe #
      iframe
    try simp only [↓reduceIte]
    icases Hpost with ⟨⟨Hpo, Hrt, Hrb⟩, Hrmo, Hcm⟩
    wsteps
    wp_apply (hMID s lid) $$ []
    · iframe #
    wsteps
    rw [decide_eq_false (Hloc hty1)]
    ihave #Ptr : isPkgInit (PROP := IProp GF)
        pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp $$ []
    · iPkgInit
    wsteps
    wp_apply (hRemovePeer γn tl c prs m.nodeId) $$ [Hlive] as Hlive
    · iframe #; iframe
    wsteps
    have hcr : ccRest true m rs = ⟨apply.bkPut (apply.bkDel rs.bk go!"members"
        (apply.memberKey m.nodeId)) go!"members_removed" (apply.memberKey m.nodeId)
        membership.removedVal, rs.mem.delete m.nodeId⟩ := by
      unfold ccRest
      rw [ite_eq_left ⟨rfl, hv⟩, ite_eq_right (by rw [hty1]; simp), ite_eq_left hty1]; rfl
    have hpa : ccPeersAfter true m rs.bk prs = prs.filter (· != m.nodeId) := by
      unfold ccPeersAfter; rw [ite_eq_left ⟨hty1, .inr hv⟩]
    rw [hcr, hpa]
    iapply HΦ
    isplitr
    · ipureintro; rfl
    iframe Hlr Hua Hdvq Hrt
    isplitl [Hcsf]
    · iexists m, csp
      iframe Hcc
      isplitr
      · ipureintro; rfl
      iunfold epConfState
      iframe Hcsf
      iunfold epCsOk; iright; iexists csm; iexact Hcsok
    isplitl [Hrb Hcm Hal Hau Hle Hbef]
    · iunfold srvRestOwnH; iunfold srvRestOwn; iunfold srvObjsOn; iunfold clusterBeOn
      iframe Hal Hau Hle
      isplitl [Hrb Hcm]
      · iframe Hrb
        iexact Hcm
      iexists mbl, lgm
      iframe Hbef Hmbe Hmlg
      ipureintro; exact Hlgmnn
    try simp only [↓reduceIte]
    isplitl [Hpo]
    · ileft; iexact Hpo
    try simp only [ccMembRes, hrd]
    iexists γn, c, γc, _
    iframe Hlive HrcG Hrmo
    ipureintro; exact Hcl))

set_option maxHeartbeats 4000000 in
theorem EtcdServer.applyConfChange.wp_proof
    (hLogger : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hValid : membership.RaftCluster.ValidateConfigurationChange.spec (GF := GF) (hG := hG))
    (hAdd : membership.RaftCluster.AddMember.spec (GF := GF) (hG := hG))
    (hRemove : membership.RaftCluster.RemoveMember.spec (GF := GF) (hG := hG))
    (hSave : schema.membershipBackend.MustSaveMemberToBackend.spec (GF := GF) (hG := hG))
    (hDelete : schema.membershipBackend.MustDeleteMemberFromBackend.spec (GF := GF) (hG := hG))
    (hRead : schema.membershipBackend.MustReadMembersFromBackend.spec (GF := GF) (hG := hG))
    (hSetCS : storage.BackendHooks.SetConfState.spec (GF := GF) (hG := hG))
    (hCAI : consistentIndex.ConsistentApplyingIndex.spec (GF := GF) (hG := hG))
    (hRemovePeer : rafthttp.Transport.RemovePeer.spec (GF := GF) (hG := hG))
    (hGetType : raftpb.ConfChange.GetType.spec (GF := GF) (hG := hG))
    (hGetNodeId : raftpb.ConfChange.GetNodeId.spec (GF := GF) (hG := hG))
    (hUnmarshal : encoding.json.Unmarshal.spec (GF := GF) (hG := hG))
    (hError : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (hBool : zap.Bool.spec (GF := GF) (hG := hG))
    (hZErr : zap.Error.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyConfChange.spec (GF := GF) (hG := hG) := by
  intro s cc ep m cs v3 ci ua E γs Pre Q Post Adv i t γB cl rs d al st lp dv ds ca k cfg cs' e
    lg bh ix lgh tl lid prs lgc cid Hok HRO Hkb HγB Hdv Hdyn Hpeer Hloc Hsz Hmem Hrem
  wp_start as ⟨#Hlg, %Hlgnn, Hlr, #Hci, Hua, #Happ, #Hrn, #Hcl, HRS, #Hclg, %Hclgnn, #Hcid, Hdvp, Hcc, Hcs, #Hbh, #Hbhi,
    #Htr, #Hmid, Hmr, Hrt, Hv3, Hpre⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply hLogger $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe; ipureintro; exact Hlgnn
  -- the rest buckets, the members and the cluster's backend field
  subst HγB
  rw [HRO]
  iunfold srvRestOwnH at HRS
  iunfold srvRestOwn at HRS
  iunfold srvObjsOn at HRS
  iunfold clusterBeOn at HRS
  icases HRS with ⟨⟨Hrb, Hcm⟩, Hal, Hau, Hle, %mbl, %lgm, %Hlgmnn, Hbef, #Hmbe, #Hmlg⟩
  ihave #Pmem : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Psch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  -- the backend's read, by its contract
  ihave #HbeRead : membership.beReadOk
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty, #mbl⟩
      iprop(backend.rbOwn d.γB rs.bk ∗ mvcc.storeRT E.γ)
      (membership.membersOfBk rs.bk).1 (membership.membersOfBk rs.bk).2 $$ []
  · iunfold membership.beReadOk
    iintro !> %Φ' !> ⟨Hrb, Hrt⟩ HΦ'
    wp_apply (hRead mbl lgm E.γ d rs.bk Hkb) $$ [Hrb Hrt] as %mp %rp ⟨Hrt, Hrb, Hmr, Hrm⟩
    · iframe #; iframe; ipureintro; exact Hlgmnn
    iapply HΦ'
    iframe
  have Hty : m.type = W32 0 ∨ m.type = W32 1 := by
    rcases Hok with ⟨h, -⟩ | ⟨-, h, -⟩
    · exact .inl h
    · exact .inr h
  have Hctx : m.type = W32 0 → ∃ i, membership.ccContextOf m.context = some (i, false) := by
    intro h0
    rcases Hok with ⟨-, -, h⟩ | ⟨-, h1, -⟩
    · exact ⟨_, h⟩
    · rw [h0] at h1; exact absurd h1 (by simp)
  ihave #Prpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Pjson : isPkgInit (PROP := IProp GF) pkg_id.encoding.json $$ []
  · iPkgInit
  ihave #Pstor : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  cases v3
  · -- without `v3` (a replay, raft's static mode): the validation answers `nil`
    have hst : γs.raft.reDyn = none := by
      cases hdv : dv with
      | none => exact Hdv hdv
      | some γn => exact absurd (Hdyn γn hdv).1 (by simp)
    have hty0 : m.type = W32 0 := by
      rcases Hok with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · rw [hst] at h; cases h
    wp_apply (hValid cl cc (DFrac.own 1) (DFrac.own 1) m false
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty, #mbl⟩
      iprop(True) ∅ ∅ Hty Hctx) $$ [Hbef Hcc] as %err ⟨Hbef, Hcc, Herr⟩
    · iframe #; iframe; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herr with %Herr
    subst Herr
    -- `s.beHooks.SetConfState(ep.confState)`
    iunfold epConfState at Hcs
    icases Hcs with ⟨Hcsf, #Hcsok⟩
    wp_pures
    wp_auto
    wp_apply (hSetCS bh ix lgh cs) $$ []
    · iframe #; iunfold epCsOk at Hcsok; iexact Hcsok
    wp_apply (hGetType.1 cc _ m) $$ [Hcc] as Hcc
    · iframe #; iframe
    rw [hty0]
    have hctx : membership.ccContextOf m.context = some (m.nodeId, false) := by
      rcases Hok with ⟨-, -, h⟩ | ⟨h, -⟩
      · exact h
      · rw [hst] at h; cases h
    wp_auto
    icases ownConfChange_context_acc' cc _ m $$ Hcc with ⟨%csl, HC, #Hcsl, Hcc⟩
    wp_auto
    irename «$r0» => Hcv
    wp_apply (hUnmarshal csl m.context DFrac.discard _ _ m.nodeId false hctx) $$ [Hcv]
      as %err ⟨%Herr, -, %v', %pus, Hcv, Hpus, Hcus, %Hv'⟩
    · iframe #; iframe
    subst Herr
    obtain ⟨Hvid, Hvprom, Hpus, Hvlrn, Hvnm⟩ := Hv'
    ihave Hcc := Hcc $$ HC
    wp_auto
    iStructNamed Hcv
    ihave %Hmnn := typedPointsto_not_null _ _ _ $$ Member
    iStructNamed Member
    iStructNamed RaftAttributes
    iStructNamed Attributes
    wp_apply (hGetNodeId.1 cc _ m) $$ [Hcc] as Hcc
    · iframe #; iframe
    imod ownConfChange_persist _ _ _ $$ Hcc with #Hcc
    rw [Hvid]
    simp only [_root_.decide_true, Bool.not_true]
    wp_auto
    rw [Hvprom]
    wp_auto
    -- `s.cluster.AddMember(&confChangeContext.Member, false)`: nothing written
    rw [Hvlrn, Hvnm]
    subst Hpus
    ihave Hm : membership.memberAt
        («$r0_ptr».[go_etcd_io.etcd.server.v3.etcdserver.api.membership.ConfigChangeContext, go!"Member"])
        1 (membership.ccMemberAt m) $$ [ID PeerURLs IsLearner Name ClientURLs Hpus Hcus]
    · iunfold membership.memberAt
      isplitr
      · ipureintro; exact Hmnn
      iexists _, _
      simp only [membership.ccMemberAt]
      iframe
    simp only [ccMembRes, hst]
    icases Hmr with ⟨#Hrc, %γn, %c, %Hcl, #Hfz, Htk⟩
    ihave #HrcG := (membership.isRaftCluster_static cl).1 $$ Hrc
    wp_apply (hAdd cl membership.rcStatic rs.mem _ (DFrac.own 1) (membership.ccMemberAt m) false lgc cid
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty, #mbl⟩
      iprop(True) iprop(True) (rcStatic_insert _ _) (Hsz hty0)) $$ [Hcm Hm Hbef]
      as ⟨Hbef, Hpost⟩
    · iframe #; iframe
      isplitr
      · ipureintro; exact Hclgnn
      simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    icases Hpost with ⟨Hcm, Hm⟩
    iunfold membership.memberAt at Hm
    icases Hm with ⟨-, %pu, %cu, ID, PeerURLs, IsLearner, Name, ClientURLs, Hpus, Hcus⟩
    wp_auto
    wp_apply (hMID s lid) $$ []
    · iframe #
    by_cases hlid : m.nodeId = lid
    · rw [hlid]
      simp only [_root_.decide_true, Bool.not_true]
      nov3_post
    · simp only [decide_eq_false hlid, Bool.not_false]
      ihave #Ptr : isPkgInit (PROP := IProp GF)
          pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp $$ []
      · iPkgInit
      wp_auto
      wp_apply (rafthttp.Transport.AddPeer_frozen γn tl c prs m.nodeId pu (Hpeer hty0 hlid))
        $$ [Htk] as Htk
      · iframe #; iframe
      nov3_post
  · -- with `v3` (`ApplyBoth`)
    simp only [↓reduceIte]
    icases Hv3 with ⟨Hwt, #Hhook, Hupd, Hlens, Hsci⟩
    -- the hook's facts, from the uber applier's options
    ihave #HhookOk : mvcc.hookOk E.γ E.P E.f $$ []
    · iunfold apply.applierFor at Happ
      icases Happ with ⟨%up, %uopts, -, #Hui⟩
      iunfold apply.uberIs at Hui
      icases Hui with ⟨-, #Hbo, -⟩
      iunfold apply.backendOptsOk at Hbo
      icases Hbo with ⟨-, -, #Hh, -⟩
      iexact Hh
    wp_apply (hValid cl cc (DFrac.own 1) (DFrac.own 1) m true
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty, #mbl⟩
      iprop(backend.rbOwn d.γB rs.bk ∗ mvcc.storeRT E.γ)
      (membership.membersOfBk rs.bk).1 (membership.membersOfBk rs.bk).2 Hty Hctx)
      $$ [Hbef Hcc Hrb Hrt] as %err ⟨Hbef, Hcc, Hres⟩
    · simp only [↓reduceIte]; iframe #; iframe
    try simp only [↓reduceIte]
    icases Hres with ⟨⟨Hrb, Hrt⟩, %Herr⟩
    have Herr' : err = GoInterface.nil ↔ membership.ccValidOn rs.bk m = true := by
      rw [Herr]; unfold membership.ccValidOn; simp
    ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
    · iPkgInit
    by_cases hv : membership.ccValidOn rs.bk m = true
    · have he : err = GoInterface.nil := Herr'.2 hv
      subst he
      clear Herr Herr'
      wp_pures
      wp_auto
      imod ownConfChange_persist _ _ _ $$ Hcc with #Hcc
      iunfold epConfState at Hcs
      icases Hcs with ⟨Hcsf, #Hcsok0⟩
      have hraftS : dv = none → γs.raft.reDyn = none ∧ ccRaftOk γs.raft.reCfg m := by
        intro h
        have hs := Hdv h
        refine ⟨hs, ?_⟩
        rcases Hok with ⟨h0, hin, -⟩ | ⟨h1, -⟩
        · exact ⟨h0, m.nodeId, hin, .inl rfl⟩
        · rw [hs] at h1; cases h1
      have hdynS : ∀ γn, dv = some γn → ∀ dec c0 h0 h1, γn.mode = .dyn dec c0 h0 h1 →
          DynCCPreOp dec ds ca cfg (ccV2Of (.v1 m)) k e cs' :=
        fun γn h dec c0 h0 h1 hm => by
          have := (Hdyn γn h).2 dec c0 h0 h1 hm
          unfold membership.ccRaftEff at this; rw [if_pos hv] at this; exact this
      raft_cc m with hraftS hdynS then succ_tail
    · cases err with
      | nil => exact absurd (Herr'.1 rfl) hv
      | ok ei =>
        clear Herr Herr'
        wp_auto
        wp_apply hBool as %f1 -
        wp_apply hZErr as %f2 -
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        wp_auto
        wp_apply hError $$ []
        · ipureintro; exact Hlgnn
        icases ownConfChange_nodeId_acc cc m $$ Hcc with ⟨%pn, HN, Hcc⟩
        simp only [go_etcd_io.raft.v3.None']
        wp_auto
        ipersist «$r0»
        ihave Hcc := Hcc $$ %«$r0_ptr» %(W64 0) HN []
        · iunfold cellRO; iright; iexact «$r0»
        imod ownConfChange_persist _ _ _ $$ Hcc with #Hcc
        have hraft0 : dv = none → γs.raft.reDyn = none ∧
            ccRaftOk γs.raft.reCfg { m with nodeId := W64 0 } := by
          intro h
          have hs := Hdv h
          refine ⟨hs, ?_⟩
          rcases Hok with ⟨h0, hin, -⟩ | ⟨h1, -⟩
          · exact ⟨h0, m.nodeId, hin, .inr rfl⟩
          · rw [hs] at h1; cases h1
        have hdyn0 : ∀ γn, dv = some γn → ∀ dec c0 h0 h1, γn.mode = .dyn dec c0 h0 h1 →
            DynCCPreOp dec ds ca cfg (ccV2Of (.v1 { m with nodeId := W64 0 })) k e cs' :=
          fun γn h dec c0 h0 h1 hm => by
            have := (Hdyn γn h).2 dec c0 h0 h1 hm
            unfold membership.ccRaftEff at this; rw [if_neg hv] at this; exact this
        raft_cc ({ m with nodeId := W64 0 }) with hraft0 hdyn0 then fail_tail

end proof

end EtcdGrove
end Perennial
