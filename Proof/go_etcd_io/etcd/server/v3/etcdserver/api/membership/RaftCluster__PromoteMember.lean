/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__PromoteMember.lean`.
Lean-first (no Rocq counterpart); route B (2026-11-25): under the cluster's mutex, the learner gauge
for the local member (`metric.gaugeSetSpec`, in `membershipInit`, as `setIsLearnerMetric`'s proof),
then, without `shouldApplyV3`, a log line; the lock's invariant given back as it was.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__PromoteMember
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.String
public import Proof.github_com.mit_pdos.etcd_grove.FirstCallee

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

set_option maxHeartbeats 1000000 in
theorem membership.RaftCluster.PromoteMember.wp_proof
    (wp_IDStr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (wp_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.PromoteMember.spec (GF := GF) (hG := hG) := by
  intro c RM id lg cid
  wp_start as ⟨#Hrc, #Hlg, #Hlgnn, #Hcid⟩
  iunfold membership.isRaftClusterG at Hrc
  icases Hrc with ⟨%γcv, #Hrc⟩
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
  icases Hinv with ⟨%ms, %mem', Hmem, %Hsz, %lid, %rp, %rm, #Hlid, Hrf, Hrm, HRMi, Hver⟩
  (try wp_auto)
  -- the learner gauge of the local member
  ihave Hmi : (go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, ⟨%g, #Hg, #HgS⟩, -⟩
  iunfold EtcdGrove.prometheus.metric.gaugeSetSpec at HgS
  wp_if_destruct
  focus
    wp_apply HgS
  all_goals
    (try wp_auto)
    -- without `shouldApplyV3`: a log line
    repeat' (first_callee
      | "String" => (wp_apply wp_IDStr $$ [] as %_ ⟨-, -⟩; iframe #)
      | "zap.String" => (wp_apply wp_String as %_ -)
      | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr; (ipureintro; rfl);
         iintro %_ ⟨-, -⟩)
      | "Info" => (wp_apply wp_Info $$ []; iexact Hlgnn)
      | wp_auto)
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmem Hrf Hrm HRMi Hver]
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
    itrivial

end proof

end EtcdGrove
end Perennial
