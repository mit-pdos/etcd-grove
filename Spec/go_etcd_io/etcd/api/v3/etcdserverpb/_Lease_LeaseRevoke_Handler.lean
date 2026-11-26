/-
`etcdserverpb._Lease_LeaseRevoke_Handler(srv, ctx, dec, interceptor)` (`api/etcdserverpb/rpc_grpc.pb.go`,
the generated server-side handler of the Lease service's `LeaseRevoke`; translated for the client lease's stage (c); the server
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

/-- **`_Lease_LeaseRevoke_Handler(srv, ctx, dec, interceptor)`** for a service value `srv` whose
type implements `LeaseServer` (a method-set fact) and whose `LeaseRevoke` meets `Spec` with the
resource `S` and the interceptors' resources `Rs`, which the chain lends the call (per-type stage
B3) (`grpcHandlerOkMd`: at the run's incoming metadata; auth-lease S3c, 2026-11-15, as `Range`'s,
for the auth-on registration's metadata spec; a plain spec is `GrpcSpec.md`'s), for messages whose
types are `*LeaseRevokeRequest`/`*LeaseRevokeResponse` (a zero `*LeaseRevokeRequest` is the
request's blank), under the chain `ics` of transparent interceptors with their resources `Rs`, for
requests with `Q` (which the decoded request has; `srvInterceptorsOk`, given `grpcSrvChainAll ics
interceptor`), with grpc's `dec` delivering the call's deposit with the right `D` (`grpcDecDepOk`:
`Spec` at the run's incoming metadata, with its receipt `Got`): decodes a new `*LeaseRevokeRequest`
and runs `srv.LeaseRevoke` through the chain; the resources come back, and the run returns what
`grpcRunOut` says (on success a response, as `any`, answering the receipt). -/
abbrev etcdserverpb._Lease_LeaseRevoke_Handler.spec : Prop :=
  ∀ (Req Rep : ProtoMsg GF) (Spec : GrpcSpecMd Req Rep) (srv : GoInterfaceOk) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) (Q : GoInterface → IProp GF) (D : IProp GF)
    (Got : (Rep.M → IProp GF) → (GoString → IProp GF) → IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
  Req.ty = etcdserverpb.LeaseRevokeRequest.ty → Rep.ty = etcdserverpb.LeaseRevokeResponse.ty →
  go.typeSetContains srv.ty etcdserverpb.LeaseServer.ty = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      (□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.LeaseRevokeRequest) -∗ Req.blank l) ∗
      grpcHandlerOkMd #(methods srv.ty go!"LeaseRevoke" srv.v) iprop(S ∗ [∗list] R ∈ Rs, R) Spec ∗ srvInterceptorsOk Q ics Rs ∗
      (□ ∀ (l : Loc) (m : Req.M), Req.recv l m -∗
        Q (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseRevokeRequest.ty) #l)) ∗
      S ∗ ([∗list] R ∈ Rs, R) ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ D ∗
      grpcDecDepOk dec Spec ci D Got ∗ grpcSrvChainAll ics ui }}
    (methodHandlerCall (@! etcdserverpb._Lease_LeaseRevoke_Handler) #(GoInterface.ok srv)
      #(GoInterface.ok ci) dec ui)
  {{ (resp err : GoInterface), RET (PairV #resp #err); S ∗ ([∗list] R ∈ Rs, R) ∗
      grpcRunOut D Got resp err }}

end spec

end EtcdGrove
end Perennial
