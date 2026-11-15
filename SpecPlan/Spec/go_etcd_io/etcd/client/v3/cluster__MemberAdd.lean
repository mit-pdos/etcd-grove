/-
`(*clientv3.cluster).MemberAdd` (`client/v3/cluster.go`).

Users: no user in scope (etcdctl, the e2e tests); snippet `clientv3client/cluster.go`
(`ReqMemberAddThenList`); the `Cluster` bundle (`clusterAt_methods`).

Proof sketch: `c.memberAdd(ctx, peerAddrs, false)` (its spec).

Changes: new (no old spec).

Margin: none.

Round 1: the call's principal per call (W0's `ctxPrin who ctx p`); the handle records its client,
ready (`clientReady`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiClient

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
`.memberAdd urls false` linearized by the caller's update (exclusive), or an error that settles
nothing. -/
def cluster.MemberAdd.spec : Prop :=
  ∀ (cl c : Loc) (γ : Cluster) (who : Principal),
  Cluster.MemberAddTriple (fun s => cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.cluster.ty @!! s)
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clusterHandle cl c γ who ∗ clientReady c) γ who false

end spec

end ClientV3
end EtcdGrove
end Perennial
