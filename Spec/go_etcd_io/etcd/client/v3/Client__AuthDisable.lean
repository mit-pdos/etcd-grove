/-
`(*clientv3.Client).AuthDisable` (`client/v3`; promoted from the embedded `Auth` interface).

Users: `examples/etcd/auth` (through the field), etcdctl.

Proof sketch: the method value dispatches through the `Auth` field (W0's `clientRest_fields`:
the field, read-only, meeting its bundle: `authAt`), whose `AuthDisable` triple (the bundle law)
is this one; so that a caller holding the client needs no dispatch lemma (as W0's `Client.Get`).

Changes: new (round 1: the completeness review's F6).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

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

/-- `c.AuthDisable(ctx, ...)`: the `Auth` contract's `AuthDisable`. -/
def Client.AuthDisable.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) ,
  Call.Triple (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"AuthDisable")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientRest c γ who) γ who []
    .authDisable

end spec

end ClientV3
end EtcdGrove
end Perennial
