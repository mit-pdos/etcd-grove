/-
`ClusterServer.MemberPromote` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Cluster/MemberPromote` (the generated `_Cluster_MemberPromote_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `Cluster.methods` through grpc (`examples/specreq/clientv3client/cluster.go`).

Proof sketch: `cs.server.PromoteMember(ctx, r.ID)` (2e's spec, over the update); errors through `togRPCError`; the reply built from the members (`membersToProtoMembers`) and `cs.header()` (ids, term, leader): its content models the answer's member list (`replyModels`).

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

/-- `ClusterServer.MemberPromote(ctx, r)` meets the contract of `/etcdserverpb.Cluster/MemberPromote`. -/
def ClusterServer.MemberPromote.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClusterServer.ty @!! go!"MemberPromote")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ clusterServerAt p s γ) (etcdUnary γ go!"/etcdserverpb.Cluster/MemberPromote") go_etcd_io.etcd.api.v3.etcdserverpb.MemberPromoteRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.MemberPromoteResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
