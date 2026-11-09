/-
`(*clientv3.cluster).MemberAdd` (`client/v3/cluster.go`).

Users: no user in scope (etcdctl, the e2e tests); snippet `clientv3client/cluster.go`
(`ReqMemberAddAnswer`); the `Cluster` bundle (`clusterAt_methods`).

Proof sketch: `c.memberAdd(ctx, peerAddrs, false)` (its spec).

Changes: new (no old spec).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `cl.MemberAdd(ctx, urls)`: the URLs checked (`types.NewURLs`: else an error, nothing sent), then
the request `.memberAdd urls false` linearized by the caller's update (exclusive), or an error that
settles nothing. -/
def cluster.MemberAdd.spec : Prop :=
  ∀ (cl : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (sl : GoSlice) (urls : List GoString),
  CheckedCallTriple (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.cluster.ty @!! go!"MemberAdd")) (Val #ctx)) (Val #sl))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clusterHandle cl γ who ∗ Context.ctxOk ctx ∗ sl ↦*□ urls) iprop(True) γ who (.memberAdd urls false) false
    (urlsValid urls) ansReply

end spec

end ClientV3
end EtcdGrove
end Perennial
