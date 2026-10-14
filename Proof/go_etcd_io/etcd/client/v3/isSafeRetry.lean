/-
Proof of `Spec/go_etcd_io/etcd/client/v3/isSafeRetry.lean` (unit P3a). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.isSafeRetry
public import Spec.go_etcd_io.etcd.client.v3.isContextError
public import Spec.errors.IsStatusErr
public import Spec.go_etcd_io.etcd.client.v3.Client__Endpoints
public import Spec.go_etcd_io.etcd.client.v3.isSafeRetryImmutableRPC
public import Spec.go_etcd_io.etcd.client.v3.isSafeRetryMutableRPC
public import Spec.go_etcd_io.etcd.client.v3.Client__GetLogger
public import Spec.go_etcd_io.etcd.client.v3.retryPolicy__String
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Warn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil backoffOk errorStringSpec)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem isSafeRetry.wp_proof
    (wp_isContextError : isContextError.spec (GF := GF) (hG := hG))
    (wp_Is : errors.IsStatusErr.spec (GF := GF) (hG := hG))
    (wp_Endpoints : Client.Endpoints.spec (GF := GF) (hG := hG))
    (wp_Imm : isSafeRetryImmutableRPC.spec (GF := GF) (hG := hG))
    (wp_Mut : isSafeRetryMutableRPC.spec (GF := GF) (hG := hG))
    (wp_GetLogger : Client.GetLogger.spec (GF := GF) (hG := hG))
    (wp_String : retryPolicy.String.spec (GF := GF) (hG := hG))
    (wp_zapString : zap.String.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    isSafeRetry.spec (GF := GF) (hG := hG) := by
  intro c err o
  wp_start as ⟨#Hc, #Ho, %Herr, #Hse⟩
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hrpc
  icases Hri with ⟨-, -, -, -, -, -, -, -, ⟨%eL, #HeL, %HeLp⟩⟩
  iunfold retryOptsAt at Ho
  icases Ho with ⟨%ov, #Hov, #Hovk⟩
  icases options_fields_ro o ov $$ Hov with ⟨#Hrp, #Hmax, #Hbf, #Hra⟩
  ihave #Hc' := Hc
  iunfold retryClientOk at Hc'
  icases Hc' with ⟨%Hcn, #Hlg, -⟩
  haveI : go.NotInterface go.uint8 := ⟨by unfold go.uint8; trivial⟩
  wp_auto
  wp_apply wp_isContextError err $$ [$Hse] as %b1 -
  cases b1
  rotate_left
  · wp_auto
    iapply HΦ; itrivial
  wp_auto
  wp_apply (wp_Is err (GoInterface.ok eL) (Or.inr ⟨eL, rfl, HeLp⟩)) $$ [$Herrs $Hse] as %b2 -
  cases b2
  rotate_left
  · wp_auto
    wp_apply wp_Endpoints c $$ [$Hc] as %sl -
    wp_if_destruct
    · iapply HΦ; itrivial
    (try wp_auto)
    wp_if_destruct
    · wp_apply wp_Imm err $$ [] as %b -
      · iframe #; ipureintro; exact Herr
      iapply HΦ; itrivial
    wp_if_destruct
    · wp_apply wp_Mut err $$ [$Hse] as %b -
      iapply HΦ; itrivial
    wp_method_call
    wp_auto
    wp_apply wp_String ov.retryPolicy' as %str -
    wp_apply wp_zapString as %f -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨Hfsl, -⟩
    wp_auto
    wp_apply wp_GetLogger c $$ [$Hlg] as %lg %Hlgn
    wp_apply wp_Warn lg _ _ $$ []
    · iframe #; ipureintro; exact Hlgn
    iapply HΦ; itrivial
  · wp_auto
    wp_if_destruct
    · wp_apply wp_Imm err $$ [] as %b -
      · iframe #; ipureintro; exact Herr
      iapply HΦ; itrivial
    wp_if_destruct
    · wp_apply wp_Mut err $$ [$Hse] as %b -
      iapply HΦ; itrivial
    wp_method_call
    wp_auto
    wp_apply wp_String ov.retryPolicy' as %str -
    wp_apply wp_zapString as %f -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨Hfsl, -⟩
    wp_auto
    wp_apply wp_GetLogger c $$ [$Hlg] as %lg %Hlgn
    wp_apply wp_Warn lg _ _ $$ []
    · iframe #; ipureintro; exact Hlgn
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
