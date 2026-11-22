/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__roundRobinQuorumBackoff.lean` (item 5, client
construction; until 2026-11-22 a trust-boundary axiom): the closure reads `len(c.Endpoints())`,
computes `quorum = n/2 + 1` (at least 1: no division by zero), logs at debug level with
`c.GetLogger()` and returns `jitterUp(w, j)` or `0`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__roundRobinQuorumBackoff
public import Spec.go_etcd_io.etcd.client.v3.Client__Endpoints
public import Spec.go_etcd_io.etcd.client.v3.Client__GetLogger
public import Spec.go_etcd_io.etcd.client.v3.jitterUp
public import Spec.go_uber_org.zap.Uint
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Float64
public import Spec.go_uber_org.zap.Logger__Debug

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (backoffOk)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.roundRobinQuorumBackoff.wp_proof
    (wp_Endpoints : Client.Endpoints.spec (GF := GF) (hG := hG))
    (wp_GetLogger : Client.GetLogger.spec (GF := GF) (hG := hG))
    (wp_jitterUp : jitterUp.spec (GF := GF) (hG := hG))
    (wp_Uint : zap.Uint.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Float64 : zap.Float64.spec (GF := GF) (hG := hG))
    (wp_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG)) :
    Client.roundRobinQuorumBackoff.spec (GF := GF) (hG := hG) := by
  intro c w j
  wp_start as #Hc
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold retryClientOk at Hc'
  icases Hc' with ⟨%Hcn, #Hlg, -⟩
  iapply wp_fupd
  wp_auto
  ipersist c
  ipersist jitterFraction
  ipersist waitBetween
  imodintro
  iapply HΦ
  unfold backoffOk
  iintro !> %a %Ψ HΨ
  wp_auto
  wp_apply wp_Endpoints c $$ [$Hc] as %sl -
  -- `quorum = n/2 + 1` is not zero: no division by zero
  have hq : uint.Z (sl.len / W64 2 + W64 1) ≠ 0 := by word
  simp only [hq, ↓reduceIte]
  wp_auto
  wp_if_destruct
  · wp_apply wp_Uint as %f0 -
    wp_apply wp_Uint as %f1 -
    wp_apply wp_Duration as %f2 -
    wp_apply wp_Float64 as %f3 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f0, f1, f2, f3]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨Hfsl, -⟩
    wp_auto
    wp_apply wp_GetLogger c $$ [$Hlg] as %lg #Hlgn
    wp_apply wp_Debug lg _ _ $$ []
    · iframe #
    wp_apply wp_jitterUp w j as %r -
    iapply HΨ
  · wp_apply wp_Uint as %f0 -
    wp_apply wp_Uint as %f1 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f0, f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨Hfsl, -⟩
    wp_auto
    wp_apply wp_GetLogger c $$ [$Hlg] as %lg #Hlgn
    wp_apply wp_Debug lg _ _ $$ []
    · iframe #
    iapply HΨ

end proof

end EtcdGrove
end Perennial
