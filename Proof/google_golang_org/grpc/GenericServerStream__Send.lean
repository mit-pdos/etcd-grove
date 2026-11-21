/-
`(*GenericServerStream[Req, Res]).Send()` over its translated body (prove-grpcext, 2026-11-20; a trust-boundary
axiom while Goose emitted no body for a method of a generic type): see
`Spec/google_golang_org/grpc/GenericServerStream__Send.lean`.
-/
module

public import Spec.google_golang_org.grpc.GenericServerStream__Send

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

theorem grpc.GenericServerStream.Send.wp_proof : grpc.GenericServerStream.Send.spec (GF := GF) (hG := hG) := by
  intro T U V W _ _ _ _ p si m Φ
  iintro ⟨#Hf, Hwp⟩
  rw [method_unfold (t := go.GoType.PointerType (google_golang_org.grpc.GenericServerStream.ty T U)) (m := go!"Send")]
  wp_auto
  wp_bind (App (Val #(methods si.ty go!"SendMsg" si.v))
    (Val #(interface.mkOk (go.GoType.PointerType U) #m : GoInterface)))
  iapply wp_wand $$ Hwp
  iintro %v ⟨%err, %Hv, HΦ⟩
  subst Hv
  wp_auto
  iexact HΦ

end proof

end EtcdGrove
end Perennial
