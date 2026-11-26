/-
Proof of `Spec/google_golang_org/grpc/StaticMethod.lean` over the real body (prove-grpcsmall,
2026-11-20; a trust-boundary axiom while grpc's `StaticMethod` was names only): grpc's
`rpc_util.go` returns `StaticMethodCallOption{}` as a `CallOption`, one of `grpcScalarOptTys`.
-/
module

public import Spec.google_golang_org.grpc.StaticMethod

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
variable [package_sem : google_golang_org.grpc.Assumptions]

theorem grpc.StaticMethod.wp_proof : grpc.StaticMethod.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply HΦ
  have h : ∃ (t : go.GoType) (x : val),
      interface.mkOk google_golang_org.grpc.StaticMethodCallOption.ty
        #(google_golang_org.grpc.StaticMethodCallOption.mk
          google_golang_org.grpc.EmptyCallOption.mk) = interface.mkOk t x ∧
      t ∈ grpcScalarOptTys := ⟨_, _, rfl, by simp [grpcScalarOptTys]⟩
  isplitl
  · unfold callOptOk
    ileft
    ipureintro
    exact h
  · ipureintro
    intro v hv
    simp only [List.mem_singleton] at hv
    subst hv
    exact h

end proof

end EtcdGrove
end Perennial
