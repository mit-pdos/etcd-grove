/-
`etcdserverpb._KV_DeleteRange_Handler(srv, ctx, dec, interceptor)` (`api/etcdserverpb/rpc_grpc.pb.go`,
the generated server-side handler of the KV service's `DeleteRange`; translated for unit P3b, the server
end of the gRPC boundary). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/google_golang_org/grpc/InvGrpc.lean`.
-/
module

public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- **`_KV_DeleteRange_Handler(srv, ctx, dec, interceptor)`** for a service value `srv` whose type
implements `KVServer` (a method-set fact) and whose `DeleteRange` meets `Spec` with the resource `S`
(`grpcHandlerOk`), for messages whose types are `*DeleteRangeRequest`/`*DeleteRangeResponse` (a zero
`*DeleteRangeRequest` is the request's blank), under the chain `ics` of transparent interceptors with
their resources `Rs`, for requests with `Q` (which the decoded request has;
`srvInterceptorsOk`, given `grpcSrvChain ics interceptor`), with grpc's
`dec` for the request at `m` and `Spec m Φ`: decodes a new `*DeleteRangeRequest` and runs `srv.DeleteRange`
through the chain; the resources come back, and on success the response (as `any`) is at some
`m'` with `Φ m'`. -/
abbrev etcdserverpb._KV_DeleteRange_Handler.spec : Prop :=
  ∀ (Req Rep : ProtoMsg GF) (Spec : GrpcSpec Req Rep) (srv : GoInterfaceOk) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) (Q : GoInterface → IProp GF) (m : Req.M)
    (Φ : Rep.M → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc)
    (C : GoInterfaceOk → IProp GF),
  Req.ty = etcdserverpb.DeleteRangeRequest.ty → Rep.ty = etcdserverpb.DeleteRangeResponse.ty →
  go.typeSetContains srv.ty etcdserverpb.KVServer.ty = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      (□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.DeleteRangeRequest) -∗ Req.blank l) ∗
      grpcHandlerOk #(methods srv.ty go!"DeleteRange" srv.v) S Spec C ∗ srvInterceptorsOk Q ics Rs C ∗
      (□ ∀ l : Loc, Req.recv l m -∗
        Q (interface.mkOk (go.GoType.PointerType etcdserverpb.DeleteRangeRequest.ty) #l)) ∗
      S ∗ ([∗list] R ∈ Rs, R) ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ C ci ∗
      grpcDecOk dec Req m ∗ grpcSrvChain ics ui ∗ Spec m Φ }}
    (methodHandlerCall (@! etcdserverpb._KV_DeleteRange_Handler) #(GoInterface.ok srv)
      #(GoInterface.ok ci) dec ui)
  {{ (resp err : GoInterface), RET (PairV #resp #err); S ∗ ([∗list] R ∈ Rs, R) ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
        ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') }}

end spec

end EtcdGrove
end Perennial
