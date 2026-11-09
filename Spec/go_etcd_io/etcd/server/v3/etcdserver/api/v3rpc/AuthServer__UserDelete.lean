/-
`AuthServer.UserDelete` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Auth/UserDelete` (the generated `_Auth_UserDelete_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `RemoteCallTriple` for the auth RPCs (`examples/specreq/clientv3client/auth.go`).

Proof sketch: `as.authenticator.UserDelete(ctx, r)` (2c's `EtcdServer.UserDelete.spec`, the update passed on); errors through `togRPCError`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/AuthServer__UserDelete.lean`: over the contract (was the auth plan's `authServerIs` with per-method answers).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `AuthServer.UserDelete(ctx, r)` meets the contract of `/etcdserverpb.Auth/UserDelete`. -/
def AuthServer.UserDelete.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"UserDelete")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ authServerAt p s γ) (etcdUnary γ go!"/etcdserverpb.Auth/UserDelete") go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserDeleteRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserDeleteResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
