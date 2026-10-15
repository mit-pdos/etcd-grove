/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/_Watch_Watch_Handler.lean` (unit W-W).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Watch_Watch_Handler

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

theorem etcdserverpb._Watch_Watch_Handler.wp_proof
    (wp_Recv : grpc.GenericServerStream.Recv.spec (GF := GF) (hG := hG))
    (wp_Send : grpc.GenericServerStream.Send.spec (GF := GF) (hG := hG))
    (wp_Context : grpc.GenericServerStream.Context.spec (GF := GF) (hG := hG)) :
    etcdserverpb._Watch_Watch_Handler.spec (GF := GF) (hG := hG) := by
  intro Req Rep Up Spec srv S γ Dn ci cd st hReq hRep hsrv
  wp_start as ⟨#Hown, #Hh, HSpec, HS, #Hraw, HRt, HSt⟩
  wp_auto
  wp_alloc p as Hp
  wp_auto
  iStructNamed Hp
  ipersist ServerStream
  have hI : IntoValTyped (GF := GF) etcdserverpb.WatchRequest Req.ty := hReq ▸ inferInstance
  have hw := srvStreamIs_of_raw (GF := GF) (Req := Req) (Rep := Rep) etcdserverpb.WatchRequest
    etcdserverpb.WatchResponse wp_Recv wp_Send wp_Context p st γ Up Dn ci cd
  rw [hReq, hRep] at hw
  ihave #Hst := hw $$ [ServerStream]
  · iframe #
  simp only [hsrv, ↓reduceIte]
  wp_auto
  iunfold grpcStreamHandlerOk at Hh
  wp_bind (App (Val #(methods srv.ty go!"Watch" srv.v)) _)
  iapply Hh $$ %γ %Dn %ci %cd %_ %_ HSpec HS Hst HRt HSt
  inext
  iintro %err
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
