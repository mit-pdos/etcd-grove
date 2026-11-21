/-
`(*GenericClientStream[Req, Res]).Context()` over its translated body (prove-grpcext, 2026-11-20; a trust-boundary
axiom while Goose emitted no body for a method of a generic type): see
`Spec/google_golang_org/grpc/GenericClientStream__Context.lean`.
-/
module

public import Spec.google_golang_org.grpc.GenericClientStream__Context

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

theorem grpc.GenericClientStream.Context.wp_proof : grpc.GenericClientStream.Context.spec (GF := GF) (hG := hG) := by
  intro T U V W _ _ _ _ p si Φ
  iintro ⟨#Hf, Hwp⟩
  rw [method_unfold (t := go.GoType.PointerType (google_golang_org.grpc.GenericClientStream.ty T U)) (m := go!"Context")]
  wp_auto
  iexact Hwp

end proof

end EtcdGrove
end Perennial
