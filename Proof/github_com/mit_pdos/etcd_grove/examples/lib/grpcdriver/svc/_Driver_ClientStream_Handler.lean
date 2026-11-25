/- Lean-first (no Rocq counterpart).

# `svc._Driver_ClientStream_Handler`'s proof

As `_Watch_Watch_Handler`'s: the wrapped end (`srvStreamIs_of_raw`) and its `SendAndClose`
(`sacOk_of_raw`), then the method's contract.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_ClientStream_Handler

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode EtcdGrove google_golang_org.protobuf.types.known

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem _Driver_ClientStream_Handler.wp_proof
    (wp_Recv : grpc.GenericServerStream.Recv.spec (GF := GF) (hG := hG))
    (wp_Send : grpc.GenericServerStream.Send.spec (GF := GF) (hG := hG))
    (wp_Context : grpc.GenericServerStream.Context.spec (GF := GF) (hG := hG)) :
    _Driver_ClientStream_Handler.spec (GF := GF) (hG := hG) := by
  intro Up Spec srv S γ Dn ci cd st hsrv
  wp_start as ⟨#Hh, HSpec, HS, #Hraw, HRt, HSt⟩
  wp_auto
  wp_alloc p as Hp
  wp_auto
  iStructNamed Hp
  ipersist ServerStream
  have hReq : (strmT (GF := GF)).ty = wrapperspb.StringValue.ty := rfl
  have hI : IntoValTyped (GF := GF) wrapperspb.StringValue (strmT (GF := GF)).ty := hReq ▸ inferInstance
  have hT : TypeRepr (strmT (GF := GF)).ty wrapperspb.StringValue := hReq ▸ inferInstance
  have hw := srvStreamIs_of_raw (GF := GF) (Req := strmT) (Rep := strmT) wrapperspb.StringValue
    wrapperspb.StringValue wp_Recv wp_Send wp_Context p st γ Up Dn ci cd
  have hs := sacOk_of_raw (GF := GF) (Req := strmT) (Rep := strmT) wrapperspb.StringValue
    wrapperspb.StringValue p st γ Up Dn ci cd
  rw [hReq] at hw hs
  ihave #Hst := hw $$ [ServerStream]
  · iframe #
    iintro !> %l Hl
    simp only [strmT, pbStringValueST, pbStringValueS]
    iexists _
    iexact Hl
  ihave #Hsac := hs $$ [ServerStream]
  · iframe #
  simp only [hsrv, ↓reduceIte]
  wp_auto
  iunfold strmMethodOk at Hh
  wp_bind (App (Val #(methods srv.ty go!"ClientStream" srv.v)) _)
  iapply Hh $$ %γ %Dn %ci %cd %_ %_ HSpec HS Hst Hsac HRt HSt
  inext
  iintro %err #Herr HS
  wp_auto
  iapply HΦ
  iframe HS
  iexact Herr

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
