/-
`clientv3.NewCluster` (`client/v3/cluster.go`).

Users: `newClient`.

Proof sketch: the retry wrapper over the client's connection (`Retry*Client`'s spec, from
`clientConnOk`), the client's `callOpts` (`callOptsOk _ false`); persisted.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/NewCluster.lean`: over `clientCore`.

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

/-- `NewCluster(c)`: a `*cluster` of the client's cluster and principal. -/
def NewCluster.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientCore c γ who }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewCluster)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ a : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.cluster.ty) #a⌝ ∗ clusterHandle a γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial
