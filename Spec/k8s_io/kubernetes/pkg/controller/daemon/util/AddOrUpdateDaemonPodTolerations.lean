/-
`util.AddOrUpdateDaemonPodTolerations(spec)` (`daemonset_util.go`): the daemon pods' default
tolerations added or updated in the pod spec (`daemonTols`). Lean-first; Stage 3, track B.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel consistency k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.util.Assumptions]

/-- **`AddOrUpdateDaemonPodTolerations(sp)`**: the spec's tolerations become `daemonTols`. -/
abbrev AddOrUpdateDaemonPodTolerations.spec : Prop :=
  ∀ (sp : Loc) (v : k8s_io.api.core.v1.PodSpec) (s : kd.core.PodSpec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.util ∗ sp ↦ v ∗ kd.core.PodSpec.own v (DFrac.own 1) s }}
    (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.util.AddOrUpdateDaemonPodTolerations)) (Val #sp))
  {{ RET #(); ∃ v', sp ↦ v' ∗ kd.core.PodSpec.own v' (DFrac.own 1)
      { s with Tolerations' := daemonTols s.HostNetwork' s.Tolerations' } }}

end spec

end dsctl
end EtcdGrove
end Perennial
