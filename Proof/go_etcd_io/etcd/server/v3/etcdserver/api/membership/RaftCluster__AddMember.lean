/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__AddMember.lean`.
Lean-first (no Rocq counterpart); D43 M5b (2026-10-26): under the cluster's mutex, the learner
metric for the local member; with `shouldApplyV3` the backend's save by the caller's triple, then
the members map whole (the lock's half and the apply thread's, `memAt_join`) gets the member, which
the log line reads before the map and the member are split into the two halves again.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__AddMember
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__updateMembershipMetric
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.setIsLearnerMetric
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_uber_org.zap.Logger__Info
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option hygiene false in
/-- The member's fields back into `memberAt m 1 mm`. -/
local macro "fold_member" : tactic => `(tactic| (
  ihave Hm : membership.memberAt m 1 mm $$ [Hid Hpu Hil Hnm Hcu Hpus Hcus]
  · iunfold membership.memberAt
    isplitr; (ipureintro; exact Hmnn)
    iexists pu, cu; iframe))

set_option hygiene false in
/-- `memberAt m 1 mm` opened into its fields. -/
local macro "open_member" : tactic => `(tactic| (
  iunfold membership.memberAt at Hm
  icases Hm with ⟨-, %pu, %cu, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩))

set_option hygiene false in
/-- A log line of the added member: the field strings, the slice literal, `Info`. -/
local macro "log_line" : tactic => `(tactic| (
  repeat' (first
    | (wp_apply wp_IDStr _ _ _ $$ [Hid] as %_ ⟨Hid, -⟩; iframe #; iexact Hid)
    | (wp_apply wp_IDStr $$ [] as %_ ⟨-, -⟩; iframe #)
    | (wp_apply wp_String as %_ -)
    | (wp_apply wp_Strings as %_ -)
    | (wp_apply wp_Bool as %_ -)
    | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
       iintro %_ ⟨-, -⟩)
    | (wp_apply wp_Info $$ []; ipureintro; exact Hlgnn)
    | wp_auto)))

set_option maxHeartbeats 1000000 in
theorem membership.RaftCluster.AddMember.wp_proof
    (wp_metric : membership.RaftCluster.updateMembershipMetric.spec (GF := GF) (hG := hG))
    (wp_learner : membership.setIsLearnerMetric.spec (GF := GF) (hG := hG))
    (wp_IDStr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (wp_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Strings : zap.Strings.spec (GF := GF) (hG := hG))
    (wp_Bool : zap.Bool.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.AddMember.spec (GF := GF) (hG := hG) := by
  intro c RM mem m dqb mm v3 lg cid bi Ps Qs HRM Hsz'
  wp_start as ⟨#Hrc, Hcm, Hm, #Hlg, %Hlgnn, #Hcid, Hbe, Hd⟩
  iunfold membership.isRaftClusterG at Hrc
  ihave %Hmnn := (show membership.memberAt (GF := GF) m 1 mm ⊢ ⌜m ≠ null⌝ by
    unfold membership.memberAt; iintro ⟨%H, -⟩; ipureintro; exact H) $$ Hm
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
  icases Hinv with ⟨%ms, %mem', Hmem, %Hsz, %lid, %rp, %rm, #Hlid, Hrf, Hrm, HRMi⟩
  open_member
  (try wp_auto)
  -- the learner metric of the local member
  wp_if_destruct
  focus
    fold_member
    wp_apply wp_learner $$ [Hm] as Hm
    · iframe
    open_member
  all_goals
    (try wp_auto)
    cases v3
    · -- without `shouldApplyV3`: a log line
      (try wp_auto)
      log_line
      wp_method_call
      wp_call
      wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmem Hrf Hrm HRMi]
      · inext
        iunfold membership.rcLockInvG
        iexists ms, mem'
        iframe Hmem
        isplitr
        · ipureintro; exact Hsz
        iexists _, rp, rm
        iframe
        iframe #
      (try wp_auto)
      iapply HΦ
      iframe Hbe
      simp only [Bool.false_eq_true, ↓reduceIte]
      fold_member
      iframe
    · -- with `shouldApplyV3`: the backend's save, by the caller's triple
      simp only [↓reduceIte]
      icases Hd with ⟨#Hsave, HPs⟩
      iunfold membership.beSaveOk at Hsave
      (try wp_auto)
      fold_member
      wp_bind (App (Val #(methods bi.ty go!"MustSaveMemberToBackend" bi.v)) (Val #m))
      iapply Hsave $$ [HPs Hm]
      · iframe
      inext
      iintro ⟨HQs, Hm⟩
      open_member
      -- the members map whole: the lock's half and the apply thread's
      iunfold membership.clusterMem at Hcm
      icases Hcm with ⟨%ms2, Hcm⟩
      icases membership.memAt_join c ms ms2 mem' mem $$ [Hmem Hcm] with ⟨%Hag, Hmem⟩
      · iframe
      obtain ⟨-, Hmeq⟩ := Hag
      subst Hmeq
      iunfold membership.memAt at Hmem
      icases Hmem with ⟨%mp, Hmf, Hmap, %Hdom, Hmems⟩
      (try wp_auto)
      wp_apply wp_mapInsert $$ [Hmap] as Hmap
      · iframe Hmap
      (try wp_auto)
      wp_apply wp_metric $$ [$Hlid]
      (try wp_auto)
      log_line
      -- the map and the member back in two halves
      fold_member
      have Hdom' := membership.memDom_insert ms mem mm.id m mm Hdom
      ihave Hmem : membership.memAt c 1 (GMap.insert mm.id m ms) (GMap.insert mm.id mm mem)
        $$ [Hmf Hmap Hmems Hm]
      · iunfold membership.memAt
        iexists mp
        iframe Hmf Hmap
        isplitr
        · ipureintro; exact Hdom'
        iapply membership.memMembers_insert $$ [Hmems Hm]
        iframe
      icases membership.memAt_halve c _ _ $$ Hmem with ⟨Hmem, Hcm⟩
      wp_method_call
      wp_call
      wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmem Hrf Hrm HRMi]
      · inext
        iunfold membership.rcLockInvG
        iexists GMap.insert mm.id m ms, GMap.insert mm.id mm mem
        iframe Hmem
        isplitr
        · ipureintro; rw [Hdom'.2]; exact Hsz'
        iexists _, rp, rm
        iframe Hrf Hrm
        iframe #
        iapply HRM $$ HRMi
      (try wp_auto)
      iapply HΦ
      iframe Hbe
      try simp only [↓reduceIte]
      iframe HQs
      iunfold membership.clusterMemIn
      iexists _
      iframe Hcm
      ipureintro; exact GMap.lookup_insert _ _ _

end proof

end EtcdGrove
end Perennial
