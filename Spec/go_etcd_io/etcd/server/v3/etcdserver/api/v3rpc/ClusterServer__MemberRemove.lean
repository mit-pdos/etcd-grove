/-
`ClusterServer.MemberRemove` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Cluster/MemberRemove` (the generated `_Cluster_MemberRemove_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `Cluster.methods` through grpc (`examples/specreq/clientv3client/cluster.go`).

Proof sketch: `cs.server.RemoveMember(ctx, r.ID)` (2e's spec, over the update); errors through `togRPCError`; the reply built from the members (`membersToProtoMembers`) and `cs.header()` (ids, term, leader): its content models the answer's member list (`replyModels`).

Changes: new (no old spec: the cluster service was names only).

Round 1: the contract is the member's at `ep` (`etcdContract γ ep`; the lease requests' `leaseFact`); the first way fires no token or learner refusal (`firedAns`: 2c returns an apply-time `ErrUserEmpty`/`ErrAuthOldRevision`/`ErrInvalidAuthToken` unfired, its outcome 2, which this handler sends by the second way); errors reach `togRPCError` with 2c's `srvErrOk`; a read composes with 2c's `SrvCallTriple` once W0's round 4 makes `srvStep` `Step` (a read's permission checked at an auth state between the call's start and its answer).

Margin: the order of the members is the server's (`clusterStep`: any permutation).
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

/-- `ClusterServer.MemberRemove(ctx, r)` meets the contract of `/etcdserverpb.Cluster/MemberRemove`. -/
def ClusterServer.MemberRemove.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster) (ep : GoString),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClusterServer.ty @!! go!"MemberRemove")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ clusterServerAt p s γ) (etcdUnary γ ep go!"/etcdserverpb.Cluster/MemberRemove") go_etcd_io.etcd.api.v3.etcdserverpb.MemberRemoveRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.MemberRemoveResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
