/-
`authSrvTP true` (`authSrvTP_on`), whose proof reaches linked results: moved out of `AuthSrv.lean`
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

/-- **`authSrvTP true`** (see the file header): the simple provider, its names the auth names'
token names, the auth names allocated over the boot state, the kit in the mode `on`. -/
theorem authSrvTP_on (h25 : auth.NewTokenProvider.spec (GF := GF) (hG := hG))
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
    (hCtxLb : auth.authStore.AuthInfoFromCtx.specLb (GF := GF) (hG := hG))
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
    (hD22 : ⊢ authSchemaSrv (GF := GF)) :
    authSrvTP (GF := GF) true := by
  intro lg opts iw ttl γy
  iintro %Φ ⟨#Hpkg, #Hlg, %Hon, #Hiw⟩ HΦ
  obtain ⟨hopts, httl⟩ := Hon rfl
  iapply (h25 lg opts iw ttl) $$ [Hpkg]
  · iframe Hpkg; iapply zapLoggerOk_orNil; iexact Hlg
  iintro !> %tp %err ⟨%Htp, Hres⟩
  iapply HΦ
  isplitr
  · ipureintro; exact Htp
  iintro %Herr
  icases Hres with (%Hno | ⟨%p, %γt, %γf, %Hp, #Hiwf, #Hok, HA, Hfr⟩)
  · exfalso; rcases Hno with h | h
    · exact h hopts
    · omega
  obtain ⟨-, rfl⟩ := Hp
  imod (auth.authBoot_alloc (GF := GF) γt γf γy) with ⟨%γa, %Hγ, Hown, Hcur, HI, Hcap, #Hcn, Hbk,
    Hsucc, HpubQ⟩
  obtain ⟨hγt, hγf, hγy⟩ := Hγ
  subst hγt hγf hγy
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
    exact ⟨rfl, fun _ => ⟨γa, rfl⟩, fun γa' h => by cases h; rfl⟩
  iapply (authStoreKit_on h_Warn h_Int h_Revision h_commit h_metrics h_refresh hCtx hCtxLb hAdminLbO hTLS hPut hRange
    hDel hAdmin hEn hPutL hRangeL hDelL hAdminL hRangeLb hRangeLbR hEnLb hRevLb hAdminLb hPutLb hEnableB hUserAddB hRoleAddB hUserGrantRoleB
    hRoleGrantPermissionB hAuthnB hCP hGT hD22 _ γa (auth.simpleAdmin p))
    $$ [$HtpA $HA $Hown $Hcur $HI $Hfr $Hcap $Hcn Hsucc $Hbk $HpubQ]
  unfold auth.authSucc; iexact Hsucc

end proof

end EtcdGrove
end Perennial
