/-
`etcdserverpb._KV_Txn_Handler(srv, ctx, dec, interceptor)` (`api/etcdserverpb/rpc_grpc.pb.go`,
the generated server-side handler of the KV service's `Txn`; translated for unit P3b, the server
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- **`_KV_Txn_Handler(srv, ctx, dec, interceptor)`** for a service value `srv` whose type
implements `KVServer` (a method-set fact) and whose `Txn` meets `Spec` with the resource `S`
(`grpcHandlerOkMd`: at the run's incoming metadata; a plain spec is `GrpcSpec.md`'s), for messages
whose types are `*TxnRequest`/`*TxnResponse` (a zero `*TxnRequest` is the request's blank), under
the chain `ics` of transparent interceptors with their resources `Rs`, for requests with `Q` (which
the decoded request has; `srvInterceptorsOk`, given `grpcSrvChain ics interceptor`), with grpc's
`dec` for the request at `m` and `Spec` of the run's metadata at `m` and `Φ`: decodes a new
`*TxnRequest` and runs `srv.Txn` through the chain; the resources come back, and on success the
response (as `any`) is at some `m'` with `Φ m'`. -/
abbrev etcdserverpb._KV_Txn_Handler.spec : Prop :=
  ∀ (Req Rep : ProtoMsg GF) (Spec : GrpcSpecMd Req Rep) (srv : GoInterfaceOk) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) (Q : GoInterface → IProp GF) (m : Req.M)
    (Φ : Rep.M → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
  Req.ty = etcdserverpb.TxnRequest.ty → Rep.ty = etcdserverpb.TxnResponse.ty →
  go.typeSetContains srv.ty etcdserverpb.KVServer.ty = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      (□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.TxnRequest) -∗ Req.blank l) ∗
      grpcHandlerOkMd #(methods srv.ty go!"Txn" srv.v) S Spec ∗ srvInterceptorsOk Q ics Rs ∗
      (□ ∀ l : Loc, Req.recv l m -∗
        Q (interface.mkOk (go.GoType.PointerType etcdserverpb.TxnRequest.ty) #l)) ∗
      S ∗ ([∗list] R ∈ Rs, R) ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗
      grpcSrvChain ics ui ∗ Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ }}
    (methodHandlerCall (@! etcdserverpb._KV_Txn_Handler) #(GoInterface.ok srv)
      #(GoInterface.ok ci) dec ui)
  {{ (resp err : GoInterface), RET (PairV #resp #err); S ∗ ([∗list] R ∈ Rs, R) ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
        ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') }}

end spec

end EtcdGrove
end Perennial
