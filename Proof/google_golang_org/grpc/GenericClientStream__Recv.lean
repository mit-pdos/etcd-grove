/-
`(*GenericClientStream[Req, Res]).Recv()` over its translated body (prove-grpcext, 2026-11-20; a trust-boundary
axiom while Goose emitted no body for a method of a generic type): see
`Spec/google_golang_org/grpc/GenericClientStream__Recv.lean`.
-/
module

public import Spec.google_golang_org.grpc.GenericClientStream__Recv

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

theorem grpc.GenericClientStream.Recv.wp_proof : grpc.GenericClientStream.Recv.spec (GF := GF) (hG := hG) := by
  intro T U V W _ _ _ _ _ _ p si Φ
  iintro ⟨#Hf, Hwp⟩
  rw [method_unfold (t := go.GoType.PointerType (google_golang_org.grpc.GenericClientStream.ty T U)) (m := go!"Recv")]
  wp_auto
  ispecialize Hwp $$ %_ «$r0»
  wp_bind (App (Val #(methods si.ty go!"RecvMsg" si.v))
    (Val #(interface.mkOk (go.GoType.PointerType U) #«$r0_ptr» : GoInterface)))
  iapply wp_wand $$ Hwp
  iintro %v ⟨%err, %Hv, HΦ⟩
  subst Hv
  rcases err with ei | _
  · rw [if_neg (by intro h; cases h)]
    wp_auto
    iexact HΦ
  · rw [if_pos rfl]
    wp_auto
    iexact HΦ

end proof

end EtcdGrove
end Perennial
