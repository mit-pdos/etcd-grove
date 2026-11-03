/-
`util.SurgeCount(ds, numberToSchedule)` (`daemonset_util.go`): `0` for a strategy other than
`RollingUpdate`, no rolling-update configuration or no `MaxSurge`; else
`intstr.GetScaledValueFromIntOrPercent(MaxSurge, n, true)` (a trust-boundary spec to propose: the
value is opaque, gap C5). Lean-first; Stage 3, track B.
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

/-- **`SurgeCount(ds, n)`**: `(0, nil)` unless surge is requested. -/
abbrev SurgeCount.spec : Prop :=
  ∀ (ds : Loc) (d : kd.apps.DaemonSet) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.util ∗ □ dsAt ds DFrac.discard d }}
    (App (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.util.SurgeCount)) (Val #ds)) (Val #n))
  {{ (s : w64) (err : GoInterface), RET (PairV #s #err); fmt.argOk err ∗
      ⌜¬ surgeReq d → s = W64 0 ∧ err = interface.nil⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
