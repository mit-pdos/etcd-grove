/-
`authSrvTPAt true` (`authSrvTPAt_on`; until #50 F7 S2 `authSrvTP_on`), whose proof reaches linked results: moved out of `AuthSrv.lean`
(2026-11-18) so that `AuthSrv.lean`, whose definitions the server's specs name (`srvAuthStoreOn`),
imports no linked result (CLAUDE.md, "Import tiers"). See `AuthSrv.lean`'s header.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSrv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [auth_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`authSrvTPAt true`** (see the file header; #50 F7 S2, P-A1: until then `authSrvTP_on`, which allocated the
names): the simple provider at the caller's token names, the boot authorities the caller's
(`auth.authBoot_given`), the kit in the mode `on γa`. -/
theorem authSrvTPAt_on (h25 : auth.NewTokenProvider.specAt (GF := GF) (hG := hG))
    (h_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (h_String : zap.String.spec (GF := GF) (hG := hG))
    (h_GTP : auth.tokenSimple.genTokenPrefix.spec (GF := GF) (hG := hG))
    (h_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h_Int : zap.Int'.spec (GF := GF) (hG := hG))
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG))
    (h_commit : auth.authStore.commitRevision.spec (GF := GF) (hG := hG))
    (h_metrics : auth.authStore.setupMetricsReporter.spec (GF := GF) (hG := hG))
    (h_refresh : auth.authStore.refreshRangePermCache.spec (GF := GF) (hG := hG))
    (hCtx : auth.authStore.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hAdminLbO : auth.authStore.IsAdminPermitted.specLbO (GF := GF) (hG := hG))
    (hTLS : auth.authStore.AuthInfoFromTLS.spec (GF := GF) (hG := hG))
    (hPut : auth.authStore.IsPutPermitted.spec (GF := GF) (hG := hG))
    (hRange : auth.authStore.IsRangePermitted.spec (GF := GF) (hG := hG))
    (hDel : auth.authStore.IsDeleteRangePermitted.spec (GF := GF) (hG := hG))
    (hAdmin : auth.authStore.IsAdminPermitted.spec (GF := GF) (hG := hG))
    (hEn : auth.authStore.IsAuthEnabled.spec (GF := GF) (hG := hG))
    (hPutL : auth.authStore.IsPutPermitted.specL (GF := GF) (hG := hG))
    (hRangeL : auth.authStore.IsRangePermitted.specL (GF := GF) (hG := hG))
    (hDelL : auth.authStore.IsDeleteRangePermitted.specL (GF := GF) (hG := hG))
    (hAdminL : auth.authStore.IsAdminPermitted.specL (GF := GF) (hG := hG))
    (hRangeLb : auth.authStore.IsRangePermitted.specLb (GF := GF) (hG := hG))
    (hRangeLbR : auth.authStore.IsRangePermitted.specLbR (GF := GF) (hG := hG))
    (hEnLb : auth.authStore.IsAuthEnabled.specLb (GF := GF))
    (hRevLb : auth.authStore.Revision.specLb (GF := GF))
    (hAdminLb : auth.authStore.IsAdminPermitted.specLb (GF := GF) (hG := hG))
    (hPutLb : auth.authStore.IsPutPermitted.specLb (GF := GF) (hG := hG))
    (hEnableB : auth.authStore.AuthEnable.specTB (GF := GF) (hG := hG))
    (hUserAddB : auth.authStore.UserAdd.specTSureB (GF := GF) (hG := hG))
    (hRoleAddB : auth.authStore.RoleAdd.specTB (GF := GF) (hG := hG))
    (hUserGrantRoleB : auth.authStore.UserGrantRole.specTB (GF := GF) (hG := hG))
    (hRoleGrantPermissionB : auth.authStore.RoleGrantPermission.specTB (GF := GF) (hG := hG))
    (hAuthnB : auth.authStore.Authenticate.specTB (GF := GF) (hG := hG))
    (hCP : auth.authStore.CheckPassword.spec (GF := GF) (hG := hG))
    (hGT : auth.authStore.GenTokenPrefix.spec (GF := GF) (hG := hG))
    (rLk : schema.authBatchTx.Lock.spec (GF := GF) (hG := hG))
    (rUn : schema.authBatchTx.Unlock.spec (GF := GF) (hG := hG))
    (rPU : schema.authBatchTx.UnsafePutUser.spec (GF := GF) (hG := hG))
    (rDU : schema.authBatchTx.UnsafeDeleteUser.spec (GF := GF) (hG := hG))
    (rPR : schema.authBatchTx.UnsafePutRole.spec (GF := GF) (hG := hG))
    (rDR : schema.authBatchTx.UnsafeDeleteRole.spec (GF := GF) (hG := hG))
    (rSE : schema.authBatchTx.UnsafeSaveAuthEnabled.spec (GF := GF) (hG := hG))
    (rSR : schema.authBatchTx.UnsafeSaveAuthRevision.spec (GF := GF) (hG := hG))
    (rGU : schema.authBatchTx.UnsafeGetUser.spec (GF := GF) (hG := hG))
    (rGR : schema.authBatchTx.UnsafeGetRole.spec (GF := GF) (hG := hG))
    (rEn : schema.authBatchTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (rRev : schema.authBatchTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (rGA : schema.authBatchTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (rBTs : schema.authBackend.BatchTx.spec (GF := GF) (hG := hG))
    (rFCs : schema.authBackend.ForceCommit.spec (GF := GF) (hG := hG))
    (rGUb : schema.authBackend.GetUser.spec (GF := GF) (hG := hG))
    (rGRb : schema.authBackend.GetRole.spec (GF := GF) (hG := hG))
    (rGAb : schema.authBackend.GetAllUsers.spec (GF := GF) (hG := hG))
    (rGARs : schema.authBackend.GetAllRoles.spec (GF := GF) (hG := hG))
    (rBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (rFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (rRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (rRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (rRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (rURr : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (rFEr : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (rLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (rUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (rCm : backend.batchTxBuffered.Commit.spec (GF := GF) (hG := hG))
    (rUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (rDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (rUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (rFE : backend.batchTxBuffered.UnsafeForEach.spec (GF := GF) (hG := hG))
    (rID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (rName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (rSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (rRTs : schema.authBackend.ReadTx.spec (GF := GF) (hG := hG))
    (rRLs : schema.authReadTx.RLock.spec (GF := GF) (hG := hG))
    (rRUs : schema.authReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (rGUt : schema.authReadTx.UnsafeGetUser.spec (GF := GF) (hG := hG))
    (rGRt : schema.authReadTx.UnsafeGetRole.spec (GF := GF) (hG := hG))
    (rEnt : schema.authReadTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (rRevt : schema.authReadTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (rGAt : schema.authReadTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (rCABs : schema.authBackend.CreateAuthBuckets.spec (GF := GF) (hG := hG))
    (rLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (rCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG)) :
    authSrvTPAt (GF := GF) true := by
  intro lg opts iw ttl γy γa
  iintro %Φ ⟨#Hpkg, #Hlg, %Hon, #Hiw, %Hy, Hfr⟩ HΦ
  obtain ⟨hopts, httl⟩ := Hon rfl
  have hy := Hy rfl
  ihave Hfr := Hfr $$ []
  · ipureintro; rfl
  iunfold authNamesFreshTP at Hfr
  icases Hfr with ⟨Htk, Hfr, Hboot⟩
  iapply (h25 lg opts iw ttl γa.tok γa.fresh) $$ [Hpkg Htk]
  · iframe Hpkg Htk; iapply zapLoggerOk_orNil; iexact Hlg
  iintro !> %tp %err ⟨%Htp, Hres⟩
  iapply HΦ
  isplitr
  · ipureintro; exact Htp
  iintro %Herr
  icases Hres with (%Hno | ⟨%p, %Hp, #Hiwf, #Hok, HA⟩)
  · exfalso; rcases Hno with h | h
    · exact h hopts
    · omega
  obtain ⟨-, rfl⟩ := Hp
  imod (auth.authBoot_given (GF := GF) γa) $$ Hboot with ⟨Hown, Hcur, HI, Hcap, #Hcn, Hbk, Hsucc, HpubQ⟩
  subst hy
  -- (auth-schema-fix S1 option A) the provider's index waiter: the caller's waiter, once ready
  ihave #Hwok : auth.simpleWaitOk p γa.rdy $$ []
  · iunfold auth.simpleWaitOk
    iexists iw
    iframe Hiwf
    iintro !> %idx
    ihave #Ht := Hiw $$ []
    · ipureintro; rfl
    ihave #Ht2 := Ht $$ %idx
    iexact Ht2
  ihave #HtpA := auth.tokenSimple_okA_run h_Debug h_String h_GTP p γa $$ [$Hpkg $Hok $Hwok]
  imodintro
  iexists (.on γa)
  isplitr
  · ipureintro
    exact ⟨rfl, fun _ => rfl, fun γa' h => by cases h; rfl⟩
  iapply (authStoreKit_on h_Warn h_Int h_Revision h_commit h_metrics h_refresh hCtx hAdminLbO hTLS hPut hRange
    hDel hAdmin hEn hPutL hRangeL hDelL hAdminL hRangeLb hRangeLbR hEnLb hRevLb hAdminLb hPutLb hEnableB hUserAddB hRoleAddB hUserGrantRoleB
    hRoleGrantPermissionB hAuthnB hCP hGT
    rLk rUn rPU rDU rPR rDR rSE rSR rGU rGR rEn rRev rGA rBTs rFCs rGUb rGRb rGAb rGARs rBT rFC rRT rRL rRU
    rURr rFEr rLI rUL rCm rUP rDel rUR rFE rID rName rSafe rRTs rRLs rRUs rGUt rGRt rEnt rRevt rGAt rCABs
    rLO rCB _ γa (auth.simpleAdmin p))
    $$ [$HtpA $HA $Hown $Hcur $HI $Hfr $Hcap $Hcn Hsucc $Hbk $HpubQ]
  unfold auth.authSucc; iexact Hsucc

end proof

end EtcdGrove
end Perennial
