/-
`(*clientv3.cluster).MemberUpdate` (`client/v3/cluster.go`).

Users: no user in scope (etcdctl); the `Cluster` bundle.

Proof sketch: `types.NewURLs` as `memberAdd`; the request; `c.remote.MemberUpdate` (non-repeatable).

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

/-- `cl.MemberUpdate(ctx, id, urls)`: the URLs checked, then the request linearized. -/
def cluster.MemberUpdate.spec : Prop :=
  ∀ (cl c : Loc) (γ : Cluster) (who : Principal),
  Cluster.MemberUpdateTriple (fun s => cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.cluster.ty @!! s) iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clusterHandle cl c γ who ∗ clientReady c) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
