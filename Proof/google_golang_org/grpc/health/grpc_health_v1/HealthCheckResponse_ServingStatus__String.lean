/-
Proof of `Spec/google_golang_org/grpc/health/grpc_health_v1/HealthCheckResponse_ServingStatus__String.lean`,
over the trusted model of protoc-gen-go's `HealthCheckResponse_ServingStatus.String`
(`TrustedCode/google_golang_org/grpc/health/grpc_health_v1.lean`, prove-healthstr, 2026-11-27,
etcd-grove#24 7225066078): the enum's four names for 0-3, else `strconv.Itoa`. (Until 2026-11-27 a
trust-boundary axiom.)
-/
module

public import Spec.google_golang_org.grpc.health.grpc_health_v1.HealthCheckResponse_ServingStatus__String
public import Spec.strconv.Itoa

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.health.grpc_health_v1.Assumptions]

theorem grpc_health_v1.HealthCheckResponse_ServingStatus.String.wp_proof
    (hItoa : strconv.Itoa.spec (GF := GF) (hG := hG)) :
    grpc_health_v1.HealthCheckResponse_ServingStatus.String.spec (GF := GF) (hG := hG) := by
  intro st
  wp_start as Hpkg
  ihave #Hsc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  -- the trusted model names the translation's type by its name
  have hty : (google_golang_org.grpc.health.grpc_health_v1.model.HealthCheckResponse_ServingStatus :
      go.GoType) = google_golang_org.grpc.health.grpc_health_v1.HealthCheckResponse_ServingStatus.ty := by
    with_unfolding_all rfl
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_auto
  wp_method_call
  wp_call
  unfold google_golang_org.grpc.health.grpc_health_v1.HealthCheckResponse_ServingStatus.String.impl
  simp only [hty]
  wp_auto
  -- the four names, then the decimal fallback
  by_cases h0 : st = W32 0
  · simp only [h0, _root_.decide_true]; wp_auto; iapply HΦ; itrivial
  simp only [h0, _root_.decide_false]; wp_auto
  by_cases h1 : st = W32 1
  · simp only [h1, _root_.decide_true]; wp_auto; iapply HΦ; itrivial
  simp only [h1, _root_.decide_false]; wp_auto
  by_cases h2 : st = W32 2
  · simp only [h2, _root_.decide_true]; wp_auto; iapply HΦ; itrivial
  simp only [h2, _root_.decide_false]; wp_auto
  by_cases h3 : st = W32 3
  · simp only [h3, _root_.decide_true]; wp_auto; iapply HΦ; itrivial
  simp only [h3, _root_.decide_false]; wp_auto
  wp_apply hItoa $$ Hsc as %str -
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
