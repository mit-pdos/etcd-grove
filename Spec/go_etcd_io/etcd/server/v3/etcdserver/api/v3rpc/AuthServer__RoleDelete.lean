/-
`AuthServer.RoleDelete` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Auth/RoleDelete` (the generated `_Auth_RoleDelete_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `RemoteCallTriple` for the auth RPCs (`examples/specreq/clientv3client/auth.go`).

Proof sketch: `as.authenticator.RoleDelete(ctx, r)` (2c's `EtcdServer.RoleDelete.spec`, the update passed on); errors through `togRPCError`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/AuthServer__RoleDelete.lean`: over the contract (was the auth plan's `authServerIs` with per-method answers).

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

/-- `AuthServer.RoleDelete(ctx, r)` meets the contract of `/etcdserverpb.Auth/RoleDelete`. -/
def AuthServer.RoleDelete.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"RoleDelete")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ authServerAt p s γ) (etcdUnary γ go!"/etcdserverpb.Auth/RoleDelete") go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleDeleteRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleDeleteResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
