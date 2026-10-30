/-
`etcdserverpb._Auth_UserGrantRole_Handler(srv, ctx, dec, interceptor)` (`api/etcdserverpb/rpc_grpc.pb.go`,
the generated server-side handler of the Auth service's `UserGrantRole`; translated for the auth plan's E3za,
as the KV service's for unit P3b). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`_Auth_UserGrantRole_Handler(srv, ctx, dec, interceptor)`** for a service value `srv` whose type
implements `AuthServer` (a method-set fact) and whose `UserGrantRole` meets `Spec` with the resource `S`, given
what it owns of the decoded request (`grpcHandlerOwnOkMd`, at the run's metadata), for messages whose types are
`*AuthUserGrantRoleRequest`/`*AuthUserGrantRoleResponse` (a zero `*AuthUserGrantRoleRequest` is the request's blank), under the chain `ics` of transparent interceptors with
their resources `Rs`, for requests with `Q` (which the decoded request has;
`srvInterceptorsOk`, given `grpcSrvChain ics interceptor`), with grpc's
`dec` for the request at `m` and `Spec` at the run's incoming metadata: decodes a new `*AuthUserGrantRoleRequest` and runs `srv.UserGrantRole`
through the chain; the resources come back, and on success the response (as `any`) is at some
`m'` with `Φ m'`. -/
abbrev etcdserverpb._Auth_UserGrantRole_Handler.spec : Prop :=
  ∀ (Req Rep : ProtoMsg GF) (Spec : GrpcSpecMd Req Rep) (srv : GoInterfaceOk) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) (Q : GoInterface → IProp GF) (m : Req.M)
    (Φ : Rep.M → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
  Req.ty = etcdserverpb.AuthUserGrantRoleRequest.ty → Rep.ty = etcdserverpb.AuthUserGrantRoleResponse.ty →
  go.typeSetContains srv.ty etcdserverpb.AuthServer.ty = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      (□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.AuthUserGrantRoleRequest) -∗ Req.blank l) ∗
      grpcHandlerOwnOkMd #(methods srv.ty go!"UserGrantRole" srv.v) S Spec ∗ srvInterceptorsOk Q ics Rs ∗
      (□ ∀ l : Loc, Req.recv l m -∗
        Q (interface.mkOk (go.GoType.PointerType etcdserverpb.AuthUserGrantRoleRequest.ty) #l)) ∗
      S ∗ ([∗list] R ∈ Rs, R) ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗
      grpcSrvChain ics ui ∗ Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ }}
    (methodHandlerCall (@! etcdserverpb._Auth_UserGrantRole_Handler) #(GoInterface.ok srv)
      #(GoInterface.ok ci) dec ui)
  {{ (resp err : GoInterface), RET (PairV #resp #err); S ∗ ([∗list] R ∈ Rs, R) ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
        ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') }}

end spec

end EtcdGrove
end Perennial
