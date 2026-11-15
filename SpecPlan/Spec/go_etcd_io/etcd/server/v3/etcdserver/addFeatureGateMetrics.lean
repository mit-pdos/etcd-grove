/-
## `addFeatureGateMetrics(fg, guageVec)` (`server.go:2491-2501`)

**Users.** `NewServer` (`server.go:332`, with the package's `serverFeatureEnabled`).

**Proof sketch.** The type assertion `fg.(*featuregate.featureGate)` (`Features.serverGate_ptr`),
its `GetAll` under the gate's lock (trusted, `pkg/v3/featuregate`), a gauge per feature
(`gaugeVecOk`: W0's metrics boundary, provisional).

**Changes** (from `specs-ref`'s `addFeatureGateMetrics.lean`): the gate by `Features.serverGate`.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.features.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Exports the feature gate's settings** as gauges. -/
def addFeatureGateMetrics.spec : Prop :=
  ∀ (fg : GoInterface) (gv : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ Features.serverGate fg ∗ gaugeVecOk gv }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.addFeatureGateMetrics)) (Val #fg)) (Val #gv))
  {{ RET #(); True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
