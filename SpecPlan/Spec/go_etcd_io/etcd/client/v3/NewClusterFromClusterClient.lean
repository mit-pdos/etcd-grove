/-
`clientv3.NewClusterFromClusterClient` (`client/v3`).

Users: `v3client.New` (the in-process client of v3lock and v3election: over an adapter, with a
`NewCtxClient` client), the gRPC proxy; snippet `clientv3client/inproc.go`.

Proof sketch: the given remote; a client's `callOpts` (or none: `callOptsOk_nil`), its logger.

Changes: new (no old spec).

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

/-- `NewClusterFromClusterClient(remote, c)`: a `*cluster` over `remote`. -/
def NewClusterFromClusterClient.spec : Prop :=
  ∀ (remote : GoInterface) (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ remoteClusterAt remote γ who ∗ (⌜c = null⌝ ∨ clientBase c who) }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.NewClusterFromClusterClient)) (Val #remote)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ a : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.cluster.ty) #a⌝ ∗
      clusterHandle a null γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
