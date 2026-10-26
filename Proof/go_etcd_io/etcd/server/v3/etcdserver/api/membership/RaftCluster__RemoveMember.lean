/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__RemoveMember.lean`.
Lean-first (no Rocq counterpart); D43 M4 (2026-10-26): under the cluster's mutex (the dynamic
instance), the backend's delete by the caller's triple, the member out of the members map (its
record kept for the log line), the removed map and its ghost halves extended together.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__RemoveMember
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__updateMembershipMetric
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Strings
public import Spec.go_uber_org.zap.Bool

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A member's peer URLs and `IsLearner`, borrowed (the rest dropped). -/
theorem membership.memberAt_log_acc (m : Loc) (q : Qp) (mm : apply.MemberM) :
    membership.memberAt (GF := GF) m q mm ⊢ ∃ (pu : GoSlice),
      membership.mPeerURLsAddr m ↦{DFrac.own q} pu ∗ pu ↦*{DFrac.own q} mm.peerURLs ∗
      membership.mIsLearnerAddr m ↦{DFrac.own q} mm.isLearner := by
  unfold membership.memberAt
  iintro ⟨%Hnn, %pu, %cu, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
  iexists pu
  iframe

set_option maxHeartbeats 1000000 in
theorem membership.RaftCluster.RemoveMember.wp_proof
    (wp_metric : membership.RaftCluster.updateMembershipMetric.spec (GF := GF) (hG := hG))
    (wp_IDStr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (wp_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Strings : zap.Strings.spec (GF := GF) (hG := hG))
    (wp_Bool : zap.Bool.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.RemoveMember.spec (GF := GF) (hG := hG) := by
  intro c γ rm mem id dqb v3 lg cid bi Pd Qd
  wp_start as ⟨#Hrc, Hw, Hcm, #Hlg, %Hlgnn, #Hcid, Hbe, Hd⟩
  iunfold membership.isRaftClusterG at Hrc
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Htypes : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hrc] as ⟨Hlocked, Hinv⟩
  iunfold membership.rcLockInvG at Hinv
  icases Hinv with ⟨%mm, %mem', Hmem, %Hsz, %lid, %rp, %rm', #Hlid, Hrf, Hrm, HRM⟩
  iunfold membership.rcDyn at HRM
  iunfold membership.rcRemovedOwn at Hw
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hw HRM
  subst Heq
  (try wp_auto)
  cases v3
  · -- without `shouldApplyV3`: a log line
    (try wp_auto)
    wp_apply wp_IDStr $$ [$Htypes $Hcid] as %s1 ⟨-, -⟩
    wp_apply wp_String as %f1 -
    (try wp_auto)
    wp_apply wp_IDStr $$ [$Htypes $Hlid] as %s2 ⟨-, -⟩
    wp_apply wp_String as %f2 -
    (try wp_auto)
    wp_apply wp_IDStr $$ [$Htypes $id] as %s3 ⟨id, -⟩
    wp_apply wp_String as %f3 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply wp_Info $$ []
    · ipureintro; exact Hlgnn
    (try wp_auto)
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmem Hrf Hrm HRM]
    · inext
      iunfold membership.rcLockInvG
      iexists mm, mem'
      iframe Hmem
      isplitr
      · ipureintro; exact Hsz
      iexists lid, rp, rm
      iframe Hrf Hrm Hlid
      iunfold membership.rcDyn
      iexact HRM
    (try wp_auto)
    iapply HΦ
    iframe Hbe
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hcm
    iunfold membership.rcRemovedOwn
    iexact Hw
  · -- with `shouldApplyV3`: the backend's delete, by the caller's triple
    simp only [↓reduceIte]
    icases Hd with ⟨#Hdel, HPd⟩
    iunfold membership.beDeleteOk at Hdel
    (try wp_auto)
    wp_bind (App (Val #(methods bi.ty go!"MustDeleteMemberFromBackend" bi.v)) (Val #id))
    iapply Hdel $$ HPd
    inext
    iintro HQd
    -- the members map whole: the lock's half and the apply thread's
    iunfold membership.clusterMem at Hcm
    icases Hcm with ⟨%ms2, Hcm⟩
    icases membership.memAt_join c mm ms2 mem' mem $$ [Hmem Hcm] with ⟨%Hag, Hmem⟩
    · iframe
    obtain ⟨-, Hmeq⟩ := Hag
    subst Hmeq
    iunfold membership.memAt at Hmem
    icases Hmem with ⟨%mp, Hmf, Hmap, %Hdom, Hmems⟩
    (try wp_auto)
    -- `m, ok := c.members[id]`, `delete(c.members, id)`, `c.removed[id] = true`
    wp_apply wp_map_lookup2 _ _ mp mm id (DFrac.own 1) $$ [$Hmap] as Hmap
    (try wp_auto)
    wp_apply wp_mapDelete mp mm id $$ [$Hmap] as Hmap
    (try wp_auto)
    wp_apply wp_mapInsert _ rp rm id true $$ [$Hrm] as Hrm
    imod dghostVar_update_halves (GMap.insert id true rm) _ _ _ $$ Hw HRM with ⟨Hw, HRM⟩
    (try wp_auto)
    wp_apply wp_metric c lid id false $$ [$Hlid]
    (try wp_auto)
    have Hsz' : GMap.size (GMap.delete id mm) ≤ 2 ^ 62 := by
      rw [GMap.map_size_delete]; split <;> omega
    cases Hm : mm !! id with
    | none =>
      -- `lg.Warn("skipped removing already removed member", ...)`
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Option.getD_none]
      (try wp_auto)
      wp_apply wp_IDStr $$ [$Htypes $Hcid] as %s1 ⟨-, -⟩
      wp_apply wp_String as %f1 -
      (try wp_auto)
      wp_apply wp_IDStr $$ [$Htypes $Hlid] as %s2 ⟨-, -⟩
      wp_apply wp_String as %f2 -
      (try wp_auto)
      wp_apply wp_IDStr $$ [$Htypes $id] as %s3 ⟨id, -⟩
      wp_apply wp_String as %f3 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply wp_Warn $$ []
      · ipureintro; exact Hlgnn
      have Hmem0 : mem !! id = none := by
        have := Hdom.1 id; rw [Hm] at this; cases h : mem !! id <;> simp_all
      ihave Hmem : membership.memAt c 1 (GMap.delete id mm) (GMap.delete id mem)
        $$ [Hmf Hmap Hmems]
      · rw [GMap.delete_notin mm id Hm, GMap.delete_notin mem id Hmem0]
        iunfold membership.memAt; iexists mp; iframe; ipureintro; exact Hdom
      icases membership.memAt_halve c _ _ $$ Hmem with ⟨Hmem, Hcm⟩
      (try wp_auto)
      wp_method_call
      wp_call
      wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmem Hrf Hrm HRM]
      · inext
        iunfold membership.rcLockInvG
        iexists GMap.delete id mm, GMap.delete id mem
        iframe Hmem
        isplitr
        · ipureintro; exact Hsz'
        iexists lid, rp, GMap.insert id true rm
        iframe Hrf Hrm Hlid
        iunfold membership.rcDyn
        iexact HRM
      (try wp_auto)
      iapply HΦ
      iframe Hbe
      try simp only [↓reduceIte]
      iframe HQd
      isplitl [Hw]
      · iunfold membership.rcRemovedOwn
        iexact Hw
      iunfold membership.clusterMem
      iexists _
      iexact Hcm
    | some m =>
      -- `lg.Info("removed member", ...)`, the member's record from the map
      simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
      icases membership.memMembers_delete 1 mm mem id m Hm $$ Hmems with ⟨Hm1, Hmems⟩
      icases membership.memberAt_log_acc m _ _ $$ Hm1 with ⟨%pu, Hpu, -, Hil⟩
      (try wp_auto)
      wp_apply wp_IDStr $$ [$Htypes $Hcid] as %s1 ⟨-, -⟩
      wp_apply wp_String as %f1 -
      (try wp_auto)
      wp_apply wp_IDStr $$ [$Htypes $Hlid] as %s2 ⟨-, -⟩
      wp_apply wp_String as %f2 -
      (try wp_auto)
      wp_apply wp_IDStr $$ [$Htypes $id] as %s3 ⟨id, -⟩
      wp_apply wp_String as %f3 -
      (try wp_auto)
      wp_apply wp_Strings as %f4 -
      (try wp_auto)
      wp_apply wp_Bool as %f5 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3, f4, f5]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply wp_Info $$ []
      · ipureintro; exact Hlgnn
      (try wp_auto)
      wp_method_call
      wp_call
      ihave Hmem : membership.memAt c 1 (GMap.delete id mm) (GMap.delete id mem)
        $$ [Hmf Hmap Hmems]
      · iunfold membership.memAt; iexists mp; iframe
        ipureintro; exact membership.memDom_delete mm mem id Hdom
      icases membership.memAt_halve c _ _ $$ Hmem with ⟨Hmem, Hcm⟩
      wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmem Hrf Hrm HRM]
      · inext
        iunfold membership.rcLockInvG
        iexists GMap.delete id mm, GMap.delete id mem
        iframe Hmem
        isplitr
        · ipureintro; exact Hsz'
        iexists lid, rp, GMap.insert id true rm
        iframe Hrf Hrm Hlid
        iunfold membership.rcDyn
        iexact HRM
      (try wp_auto)
      iapply HΦ
      iframe Hbe
      try simp only [↓reduceIte]
      iframe HQd
      isplitl [Hw]
      · iunfold membership.rcRemovedOwn
        iexact Hw
      iunfold membership.clusterMem
      iexists _
      iexact Hcm

end proof

end EtcdGrove
end Perennial
