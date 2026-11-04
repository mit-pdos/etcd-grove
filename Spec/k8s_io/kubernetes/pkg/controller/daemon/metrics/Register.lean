/-
`metrics.Register()` (`pkg/controller/daemon/metrics`, with body): registers the controller's
counter in the legacy registry, once (`registerMetrics.Do`). Lean-first, track C of the DaemonSet run.

`legacyregistry.MustRegister` panics on a name already registered: the caller gives the right to
register the counter's name (`prometheus.nameFree dsMetricName`, from program start: the closed
theorem's pure premise `prometheus.namesUnclaimed`, D16, as k8setcd3's; review 1 (API), M4). The
right is spent by the call (the `Once` registers at most once). **Margin**: the legacy registry is
component-base's own `KubeRegistry`, not prometheus's default registry, which `nameFree` is about;
the right stands in for a legacy-registry right (the run's report).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.LifeDefs
public import GeneratedProof.k8s_io.kubernetes.pkg.controller.daemon.metrics

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [met_sem : k8s_io.kubernetes.pkg.controller.daemon.metrics.Assumptions]

/-- `metrics.Register()`, with the right to register the counter's name: returns. -/
abbrev dsmetrics.Register.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.metrics ∗
      prometheus.nameFree dsMetricName }}
    (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.metrics.Register)) (Val #()))
  {{ RET #(); True }}

end spec

end dsctl
end EtcdGrove
end Perennial
