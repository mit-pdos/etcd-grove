/-
`metrics.Register()` (`pkg/controller/daemon/metrics`, with body): registers the controller's
counter in the legacy registry, once (`registerMetrics.Do`). Lean-first, track C of the DaemonSet run.

`legacyregistry.MustRegister` panics on a name already registered: the proof needs the counter's
name unclaimed (as prometheus's `namesUnclaimed`, D16), which the closed theorem would take as a
pure premise over the program; open (the run's report).
-/
module

public import Proof.k8s_io.kubernetes.Base
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

/-- `metrics.Register()`: returns. -/
abbrev dsmetrics.Register.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.metrics }}
    (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.metrics.Register)) (Val #()))
  {{ RET #(); True }}

end spec

end dsctl
end EtcdGrove
end Perennial
