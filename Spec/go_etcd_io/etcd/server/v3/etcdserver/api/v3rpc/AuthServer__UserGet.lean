/-
`AuthServer.UserGet` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Auth/UserGet` (the generated `_Auth_UserGet_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `RemoteCallTriple` for the auth RPCs (`examples/specreq/clientv3client/auth.go`).

Proof sketch: `as.authenticator.UserGet(ctx, r)` (2c's `EtcdServer.UserGet.spec`, the update passed on); errors through `togRPCError`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/AuthServer__UserGet.lean`: over the contract (was the auth plan's `authServerIs` with per-method answers).

Round 1: the contract is the member's at `ep` (`etcdContract γ ep`; the lease requests' `leaseFact`); the first way fires no token or learner refusal (`firedAns`: 2c returns an apply-time `ErrUserEmpty`/`ErrAuthOldRevision`/`ErrInvalidAuthToken` unfired, its outcome 2, which this handler sends by the second way); errors reach `togRPCError` with 2c's `srvErrOk`; a read composes with 2c's `SrvCallTriple` once W0's round 4 makes `srvStep` `Step` (a read's permission checked at an auth state between the call's start and its answer).

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

/-- `AuthServer.UserGet(ctx, r)` meets the contract of `/etcdserverpb.Auth/UserGet`. -/
def AuthServer.UserGet.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster) (ep : GoString),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"UserGet")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ authServerAt p s γ) (etcdUnary γ ep go!"/etcdserverpb.Auth/UserGet") go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserGetRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserGetResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
