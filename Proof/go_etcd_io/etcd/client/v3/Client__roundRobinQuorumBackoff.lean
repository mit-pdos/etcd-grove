/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__roundRobinQuorumBackoff.lean` (PR etcd#20731).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__roundRobinQuorumBackoff
public import Spec.go_etcd_io.etcd.client.v3.Client__Endpoints
public import Spec.go_etcd_io.etcd.client.v3.Client__GetLogger
public import Spec.go_etcd_io.etcd.client.v3.expBackoff
public import Spec.go_etcd_io.etcd.client.v3.jitterUp
public import Spec.go_uber_org.zap.Uint
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Float64
public import Spec.go_uber_org.zap.Logger__Debug

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_uber_org
open go_etcd_io.etcd.cache.v3 (backoffOk)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- The quorum `n/2 + 1` of a `uint` is never 0. -/
theorem rrQuorum_ne_zero (n : w64) : uint.Z (n / W64 2 + W64 1) ≠ 0 := by
  word

theorem Client.roundRobinQuorumBackoff.wp_proof
    (wp_Endpoints : Client.Endpoints.spec (GF := GF) (hG := hG))
    (wp_GetLogger : Client.GetLogger.spec (GF := GF) (hG := hG))
    (wp_expBackoff : expBackoff.spec (GF := GF) (hG := hG))
    (wp_jitterUp : jitterUp.spec (GF := GF) (hG := hG))
    (wp_zapUint : zap.Uint.spec (GF := GF) (hG := hG))
    (wp_zapDuration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_zapFloat64 : zap.Float64.spec (GF := GF) (hG := hG))
    (wp_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG)) :
    Client.roundRobinQuorumBackoff.spec (GF := GF) (hG := hG) := by
  intro c wb jf ex mw
  wp_start as #Hc
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold retryClientOk at Hc'
  icases Hc' with ⟨%Hcn, #Hlg, -⟩
  iapply wp_fupd
  wp_auto
  ipersist c
  ipersist waitBetween
  ipersist jitterFraction
  ipersist backoffExponent
  ipersist maxWaitBetween
  imodintro
  simp only [recv_eq_func_mk]
  iapply HΦ
  unfold backoffOk
  iintro !> %a %Φ' HΦ'
  wp_auto
  wp_apply wp_Endpoints c $$ [$Hc] as %sl -
  simp only [rrQuorum_ne_zero, ↓reduceIte]
  wp_auto
  wp_if_destruct
  · simp only [rrQuorum_ne_zero, ↓reduceIte]
    wp_auto
    wp_apply wp_zapUint as %f0 -
    wp_apply wp_zapUint as %f1 -
    wp_apply wp_zapUint as %f2 -
    wp_apply wp_zapDuration as %f3 -
    wp_apply wp_zapFloat64 as %f4 -
    wp_apply wp_zapFloat64 as %f5 -
    wp_apply wp_zapDuration as %f6 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f0, f1, f2, f3, f4, f5, f6]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨Hfsl, -⟩
    wp_auto
    wp_apply wp_GetLogger c $$ [$Hlg] as %lg %Hlgn
    wp_apply wp_Debug lg _ _ $$ []
    · iframe #; ipureintro; exact Hlgn
    wp_apply wp_expBackoff as %d -
    wp_apply wp_jitterUp as %d' -
    iapply HΦ'
  · wp_apply wp_zapUint as %f0 -
    wp_apply wp_zapUint as %f1 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f0, f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨Hfsl, -⟩
    wp_auto
    wp_apply wp_GetLogger c $$ [$Hlg] as %lg %Hlgn
    wp_apply wp_Debug lg _ _ $$ []
    · iframe #; ipureintro; exact Hlgn
    iapply HΦ'

end proof

end EtcdGrove
end Perennial
