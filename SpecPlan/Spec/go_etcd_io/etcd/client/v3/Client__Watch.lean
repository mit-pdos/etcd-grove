/-
`(*clientv3.Client).Watch` (promoted from the embedded `Watcher`; `client/v3/client.go`).

**Users**: every watch user of a `*Client` (`watcher__Watch.lean` lists them). **Proof sketch**:
the promoted method loads `c.Watcher` (`isClient_fields`: read-only, `watcherAt`) and calls its
`Watch` (`watcherAt_methods`). **Changes**: new (the old specs called the `*watcher` directly).
**Margin**: as `watcher.Watch.spec`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiWatch

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

/-- `Client.Watch` meets `Watcher.WatchTriple`, for a client of `γ` as `who`. -/
def Client.Watch.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  Watcher.WatchTriple (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Watch")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isClient c γ who)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
