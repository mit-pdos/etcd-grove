/- Lean-first (no Rocq counterpart).

# `svc._Driver_ServerStream_Handler`'s proof

`RecvMsg` on the raw end into a fresh `Msg`: an error is returned (`io.EOF`'s value, `eof_srvErrOk`,
or a status error); a request `v` (the receiver's token at `[v]`) goes, with the wrapped end
(`srvStreamIs_of_raw`), to the method's contract.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_ServerStream_Handler

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

theorem _Driver_ServerStream_Handler.wp_proof
    (wp_Recv : grpc.GenericServerStream.Recv.spec (GF := GF) (hG := hG))
    (wp_Send : grpc.GenericServerStream.Send.spec (GF := GF) (hG := hG))
    (wp_Context : grpc.GenericServerStream.Context.spec (GF := GF) (hG := hG)) :
    _Driver_ServerStream_Handler.spec (GF := GF) (hG := hG) := by
  intro Up Spec srv S γ Dn ci cd st hsrv
  wp_start as ⟨#Hh, HSpec, HS, #Hraw, HRt, HSt⟩
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hraw' := Hraw
  iunfold srvRawStreamIsW at Hraw'
  icases Hraw' with ⟨%si, %Hst, #HRecv, -⟩
  subst Hst
  wp_auto
  ihave Hm : iprop((strmT (GF := GF)).own «$r0_ptr») $$ [«$r0»]
  · simp only [strmT, pbStringValueS]
    iexists _
    iexact «$r0»
  have hty : msgAny (strmT (GF := GF)).ty «$r0_ptr» =
      interface.mkOk (go.GoType.PointerType Msg.ty) #«$r0_ptr» := rfl
  rw [← hty]
  wp_bind (App (Val #(methods si.ty go!"RecvMsg" si.v)) _)
  iapply HRecv $$ %([] : List GoString) %«$r0_ptr» [HRt Hm]
  · iframe
  iintro !> %err Hres
  icases Hres with (⟨%Herr, %v, Hrv, -, HRt⟩ | ⟨#Heof, %Hne, HRt, -, -⟩ |
    ⟨%Hne, #Hse, #Hso, HRt, -, -⟩)
  · subst Herr
    wp_auto
    wp_alloc p as Hp
    wp_auto
    iStructNamed Hp
    ipersist ServerStream
    have hReq : (strmT (GF := GF)).ty = wrapperspb.StringValue.ty := rfl
    have hI : IntoValTyped (GF := GF) wrapperspb.StringValue (strmT (GF := GF)).ty :=
      hReq ▸ inferInstance
    have hT : TypeRepr (strmT (GF := GF)).ty wrapperspb.StringValue := hReq ▸ inferInstance
    have hw := srvStreamIs_of_raw (GF := GF) (Req := strmT) (Rep := strmT) wrapperspb.StringValue
      wrapperspb.StringValue wp_Recv wp_Send wp_Context p (GoInterface.ok si) γ Up Dn ci cd
    rw [hReq] at hw
    ihave #Hst := hw $$ [ServerStream]
    · iframe #
      iintro !> %l Hl
      simp only [strmT, pbStringValueS]
      iexists _
      iexact Hl
    simp only [hsrv, ↓reduceIte]
    wp_auto
    iunfold ssMethodOk at Hh
    ihave HRt : iprop(srvRecvTok (Req := strmT (GF := GF)) γ [v]) $$ [HRt]
    · iexact HRt
    wp_bind (App (App (Val #(methods srv.ty go!"ServerStream" srv.v)) _) _)
    iapply Hh $$ %γ %Dn %ci %cd %_ %_ %v %_ HSpec HS Hst Hrv HRt HSt
    inext
    iintro %err #Herr HS
    wp_auto
    iapply HΦ
    iframe HS
    iexact Herr
  · cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe HS
      iapply eof_srvErrOk
      iframe #
  · cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe HS
      iapply go_etcd_io.etcd.cache.v3.srvErrOk_of_statusErrOk $$ Hso

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
