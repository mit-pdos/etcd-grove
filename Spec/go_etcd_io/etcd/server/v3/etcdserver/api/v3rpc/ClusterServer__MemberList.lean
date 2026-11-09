/-
`ClusterServer.MemberList` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Cluster/MemberList` (the generated `_Cluster_MemberList_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `Cluster.methods` through grpc (`examples/specreq/clientv3client/cluster.go`).

Proof sketch: `cs.server.MemberList(ctx, r)` (2e's spec: linearizable or the member's view, `clusterStep`'s `memberList`); errors through `togRPCError`; the reply built from the members (`membersToProtoMembers`) and `cs.header()` (ids, term, leader): its content models the answer's member list (`replyModels`).

Changes: new (no old spec: the cluster service was names only).

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

/-- `ClusterServer.MemberList(ctx, r)` meets the contract of `/etcdserverpb.Cluster/MemberList`. -/
def ClusterServer.MemberList.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClusterServer.ty @!! go!"MemberList")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ clusterServerAt p s γ) (etcdUnary γ go!"/etcdserverpb.Cluster/MemberList") go_etcd_io.etcd.api.v3.etcdserverpb.MemberListRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.MemberListResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
