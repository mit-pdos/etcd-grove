/-
`(*clientv3.Client).MemberAddAsLearner` (`client/v3`; promoted from the embedded `Cluster` interface).

Users: etcdctl, the e2e tests.

Proof sketch: the method value dispatches through the `Cluster` field (W0's `clientRest_fields`:
the field, read-only, meeting its bundle: `clusterAt`), whose `MemberAddAsLearner` triple (the bundle law)
is this one; so that a caller holding the client needs no dispatch lemma (as W0's `Client.Get`).

Changes: new (round 1: the completeness review's F6).

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiLease

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

/-- `c.MemberAddAsLearner(ctx, urls)`: the `Cluster` contract's. -/
def Client.MemberAddAsLearner.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  Cluster.MemberAddTriple (fun s => c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! s) iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientRest c γ who) γ who true

end spec

end ClientV3
end EtcdGrove
end Perennial
