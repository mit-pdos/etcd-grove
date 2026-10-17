/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/healthNotifier__startServe.lean` (item 4, the server
start). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.healthNotifier__startServe
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.google_golang_org.grpc.health.Server__SetServingStatus
public import Spec.google_golang_org.grpc.health.grpc_health_v1.HealthCheckResponse_ServingStatus__String

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.healthNotifier.startServe.wp_proof
    (hStr : zap.String.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hSet : health.Server.SetServingStatus.spec (GF := GF) (hG := hG))
    (hSS : grpc_health_v1.HealthCheckResponse_ServingStatus.String.spec (GF := GF) (hG := hG)) :
    v3rpc.healthNotifier.startServe.spec (GF := GF) (hG := hG) := by
  intro hc hs lg
  wp_start as ⟨#Hhs, #Hh, #Hlg, %Hlgn⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  simp only [v3rpc.allGRPCServices]
  wp_apply (hStr _ _) as %f1 -
  (try wp_auto)
  wp_apply (hSS _) as %st -
  wp_apply (hStr _ _) as %f2 -
  (try wp_auto)
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) (l := [f1, f2])
  isplitr
  · ipureintro; rfl
  iintro %zsl ⟨-, -⟩
  (try wp_auto)
  wp_apply (hInfo lg _ _)
  · iframe #; ipureintro; exact Hlgn
  (try wp_auto)
  wp_apply (hSet hs _ _)
  · iframe #
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
