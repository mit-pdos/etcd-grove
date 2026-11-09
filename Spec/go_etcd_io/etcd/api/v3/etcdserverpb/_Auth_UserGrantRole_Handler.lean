/-
`_Auth_UserGrantRole_Handler(srv, ctx, dec, interceptor)` (`api/etcdserverpb/rpc_grpc.pb.go`, generated): the
server-side handler of `/etcdserverpb.Auth/UserGrantRole`.

Users: grpc's `Serve` (2a: `regsOk`, from `Auth_ServiceDesc`'s `MethodDesc`), for the service value
`v3rpc` registers (`RegisterAuthServer`).
Proof sketch: `new(AuthUserGrantRoleRequest)` (a fresh message: some content), `dec(in)` (`Grpc.decOk_call`: the
request's content, no error), then `handlerBodyWP`: the type assertion `srv.(AuthServer)` (the
premise), the method directly or through the interceptor (with a `*UnaryServerInfo` and the closure
`func(ctx, req) { return srv.(AuthServer).UserGrantRole(ctx, req.(*AuthUserGrantRoleRequest)) }`). 2a composes it with
`icChain_call` and the method's `HandlerTriple` into `Grpc.unaryOk`.
Changes: from `specs-ref/Spec/go_etcd_io/etcd/api/v3/etcdserverpb/_Auth_UserGrantRole_Handler.lean`: WP form over grpc's `decOk` and the request's content (2a), instead of the old `grpcHandlerOkMd` over caller-built `ProtoMsg`s (`specs-ref/notes/grpc-msg-models.md`); the interceptor chain is 2a's (`icChain_call`).
Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI EtcdModel EtcdWire
open go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `_Auth_UserGrantRole_Handler(srv, ctx, dec, ic)`: decode the request, then run `handlerBodyWP` (WP form). -/
def _Auth_UserGrantRole_Handler.spec : Prop :=
  ∀ (srv : GoInterfaceOk) (ctx : GoInterface) (dec : val) (ic : GoFunc) (c : Proto.Content)
    (Ψ : val → IProp GF),
  go.typeSetContains srv.ty etcdserverpb.AuthServer.ty = true →
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ Grpc.decOk dec etcdserverpb.AuthUserGrantRoleRequest.ty c ∗
    (∀ q : Loc, Proto.msgAt etcdserverpb.AuthUserGrantRoleRequest.ty q (DFrac.own 1) c -∗
      handlerBodyWP srv go!"UserGrantRole" etcdserverpb.AuthUserGrantRoleRequest.ty etcdserverpb.AuthUserGrantRoleResponse.ty go!"/etcdserverpb.Auth/UserGrantRole"
        ctx q ic Ψ) ⊢
  WP (App (App (App (App (Val (@! etcdserverpb._Auth_UserGrantRole_Handler)) (Val #(GoInterface.ok srv)))
    (Val #ctx)) (Val dec)) (Val #ic)) {{ Ψ }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
