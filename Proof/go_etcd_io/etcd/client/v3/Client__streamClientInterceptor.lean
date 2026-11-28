/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__streamClientInterceptor.lean` (phase7-s3-interceptor,
S3.4, 2026-11-26), over `retry_interceptor.go`'s body: until then a trust-boundary axiom. Lean-first
(no Rocq counterpart).

The interceptor builds its options (`reuseOrNewWithCallOptions(defaultOptions, optFuncs)`) and returns
its closure, whose contract (`etcdStreamIcOk`) is proved once the client is ready (`etcdStreamIcOkG`):
`withVersion(ctx)`, `getToken` (a unary call on the client's connection, lent the caller's level-0
token), the call options split (`filterCallOptions`) and applied to a copy of its options; at `max = 0`
grpc's streamer on `withVersion`'s context, whose stream it returns as it is; otherwise, for the client
stream the contract takes, `Unimplemented` (`status.Errorf`). The retrying stream
(`serverStreamingRetryingStream`, a server stream at `max > 0`) is not reached.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__streamClientInterceptor
public import Spec.go_etcd_io.etcd.client.v3.reuseOrNewWithCallOptions
public import Spec.go_etcd_io.etcd.client.v3.withVersion
public import Spec.go_etcd_io.etcd.client.v3.filterCallOptions
public import Spec.go_etcd_io.etcd.client.v3.Client__getToken
public import Spec.go_etcd_io.etcd.client.v3.Client__GetLogger
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Error
public import Spec.google_golang_org.grpc.status.Errorf
public import Proof.go_etcd_io.etcd.client.v3.CtxErrLeaf
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 1600000 in
theorem Client.streamClientInterceptor.wp_proof
    (wp_reuse : reuseOrNewWithCallOptions.spec (GF := GF) (hG := hG))
    (wp_withVersion : withVersion.spec (GF := GF) (hG := hG))
    (wp_getToken : Client.getToken.spec (GF := GF) (hG := hG))
    (wp_filter : filterCallOptions.spec (GF := GF) (hG := hG))
    (wp_GetLogger : Client.GetLogger.spec (GF := GF) (hG := hG))
    (wp_zapError : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (wp_Errorf : status.Errorf.spec (GF := GF) (hG := hG)) :
    Client.streamClientInterceptor.spec (GF := GF) (hG := hG) := by
  intro c sl ros
  wp_start as ⟨#Hc, #Hsl, #Hros⟩
  ihave Hci : (go_etcd_io.etcd.cache.v3.clientv3Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, ⟨%dp, %dov, #Hdp, #Hdov, #Hdbf, %Hdpol⟩, -⟩
  ihave #Hros' := optApplyKeeps_of_ok ros $$ Hros
  wp_auto
  ipersist c
  wp_apply_raw wp_reuse dp sl ros false $$ []
  · iframe Hros' Hsl Hpkg
    unfold retryOptsAt
    iexists dov
    iframe Hdov
    unfold optionsOk
    iapply backoffOkT_of $$ Hdbf
  inext
  iintro %io ⟨#Hio, -, -⟩
  wp_pures
  wp_alloc intOpts_ptr as intOpts
  wp_pures
  wp_store
  ipersist intOpts
  wp_auto
  iapply HΦ
  iclear «$res0»
  unfold etcdStreamIcOkG
  iintro !> %cconn %ceps %cic #Hready #Hcg #Hicg
  unfold etcdStreamIcOk streamIcOk
  iintro !> %conn %addrs %method %Req %Rep %hreq %hrep %Up %Spec %ctx %cd %om %desc %opts %vs %R
    %str %Ψ !> ⟨#Hstr, %HR, HRr, #Hreg, #Hctx, #Hom, ⟨%sd, #Hsd, %Hsdc⟩, #Hopts, #Hok⟩ HΨ
  have HRe : R = levelTok 0 := HR
  subst HRe
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold retryClientOk at Hc'
  icases Hc' with ⟨%Hcn, #Hlg, -⟩
  (try wp_auto)
  wp_apply wp_withVersion ctx cd om $$ [$Hctx $Hom] as %c' ⟨%ci, %vsv, %Hc'', #Hctx', %vver, #Hver⟩
  subst Hc''
  (try wp_auto)
  ihave #Hec : iprop(▷ isEtcdConn cconn ceps) $$ []
  · inext
    iapply isEtcdConn_of_ready
    iframe Hready Hcg Hicg
  wp_apply wp_getToken c cconn ceps ci { cd with Values := vsv } $$ [$Hc $Hready $Hec $Hctx' $HRr]
    as %err ⟨HRr, #Herr, -⟩
  (try wp_auto)
  cases err with
  | ok e =>
    (try wp_auto)
    wp_apply wp_zapError as %f1 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply wp_GetLogger c $$ [$Hlg] as %lg #Hlgn
    wp_apply wp_Error lg _ _ $$ []
    · iexact Hlgn
    (try wp_auto)
    iapply HΨ
    iframe HRr
    iright
    isplitr
    · ipureintro; rfl
    iunfold clientErrOk at Herr
    unfold cliOpenErr
    icases Herr with ⟨%Hce, #Hse, #Hcl⟩
    iframe Hse Hcl
    ipureintro
    exact ⟨(by intro h; cases h), Hce (by intro h; cases h)⟩
  | nil =>
    (try wp_auto)
    wp_apply wp_filter opts vs (fun f => optApplyKeep f false) (fun _ => inferInstance) $$ [$Hopts]
      as %g %r ⟨%gs, %ros', Hg, Hgc, %Hgs, Hr, #Hros2, %Hnone⟩
    · iapply streamCallOptsOk_A $$ Hok
    (try wp_auto)
    ipersist Hr
    wp_apply wp_reuse io r ros' false $$ [] as %co ⟨#Hco, -, -⟩
    · iframe Hros2 Hr Hio
    (try wp_auto)
    ihave #Hco' := Hco
    iunfold retryOptsAt at Hco'
    icases Hco' with ⟨%cov, #Hcov, -⟩
    ihave ⟨#Hpol, #Hmax, #Hbf, #Hra⟩ := options_fields_ro co cov $$ Hcov
    (try wp_auto)
    wp_if_destruct
    · -- `max = 0`: grpc's streamer, its stream returned as it is
      ipersist Hg
      ihave #Hgok : streamCallOptsOk (GF := GF) gs $$ []
      · iapply streamCallOptsOk_scalar gs Hgs
      iunfold grpcStreamerOk at Hstr
      wp_apply Hstr $$ %method %Req %Rep %hreq %hrep %Up %Spec %ci %{ cd with Values := vsv }
          %(metadata.mdSet om go!"client-api-version" [vver]) %desc %g %gs %(levelTok 0) [HRr]
        as %cs %err' ⟨HRr, Hres⟩
      · iframe HRr Hreg Hctx' Hver Hg Hgok
        isplitr
        · ipureintro; rfl
        iexists sd
        iframe Hsd
        ipureintro; exact Or.inl Hsdc
      (try wp_auto)
      iapply HΨ
      iframe HRr
      icases Hres with (⟨%Herr', %γ, %Dn, %cd', #Hcs, Hst', Hrt, #Hsp⟩ | ⟨%Hcs, #Herr'⟩)
      · ileft
        isplitr
        · ipureintro; exact Herr'
        iexists γ, Dn, cd'
        iframe Hst' Hrt Hsp
        iapply (cliStreamIs_mono cs γ Req.toStreamMsg Rep.toStreamMsg Up _ _ Dn cd' clientRes
          grpcErrShape (fun _ => iprop(True))) $$ [] [] Hcs
        · iintro !> %a %md ⟨%Ha, #Hmd⟩
          isplitr
          · ipureintro; exact Ha
          unfold streamAttemptMd
          iexists _
          iframe Hmd
          ipureintro; exact ⟨vver, rfl⟩
        · iintro !> %e -; itrivial
      · iright
        isplitr
        · ipureintro; exact Hcs
        iapply cliOpenErr_of_cliStreamErr $$ Herr'
    · -- `max > 0` on a client stream: `Unimplemented`
      ihave #Hsd' := Hsd
      iStructNamed Hsd'
      (try wp_auto)
      simp only [Hsdc, ↓reduceIte]
      (try wp_auto)
      wp_apply wp_Errorf as %ue ⟨%Hue, #Hues, -, %Huty, -, -, -⟩
      · ipureintro
        simp only [google_golang_org.grpc.codes.OK]
        exact ⟨fun h => absurd (go.intoVal_inj h) (by decide), by decide⟩
      (try wp_auto)
      iapply HΨ
      iframe HRr
      iright
      isplitr
      · ipureintro; rfl
      unfold cliOpenErr
      iframe Hues
      cases ue with
      | nil => exact absurd rfl Hue
      | ok ui =>
        have hty := Huty ui rfl
        ihave #Hus := Hues
        unfold go_etcd_io.etcd.cache.v3.statusErrOk
        ihave ⟨-, %Hleaf, -⟩ := Hus $$ %ui %rfl
        isplitr
        · ipureintro
          exact ⟨Hue, clientErr_statusError ui Hleaf hty EtcdGrove.rpctypesEtcdError_asTarget⟩
        iapply go_etcd_io.etcd.cache.v3.errCellOk_of_ty
        rw [hty]
        simp [google_golang_org.grpc.internal.status.Error.ty, _root_.Perennial.errors.errorString.ty]

end proof

end EtcdGrove
end Perennial
