/-
`util.AllowsSurge(ds)` (`daemonset_util.go`): `SurgeCount(ds, 1)` is positive with no error.
Lean-first; Stage 3, track B. With surge not requested (`surgeReq`) it is `false`; otherwise any
boolean (`intstr.GetScaledValueFromIntOrPercent` of the opaque `MaxSurge`, gap C5).
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

/-- **`AllowsSurge(ds)`**: `false` unless surge is requested. -/
abbrev AllowsSurge.spec : Prop :=
  ∀ (ds : Loc) (d : kd.apps.DaemonSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.util ∗ □ dsAt ds DFrac.discard d }}
    (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.util.AllowsSurge)) (Val #ds))
  {{ (b : Bool), RET #b; ⌜¬ surgeReq d → b = false⌝ }}

end spec

end dsctl
end EtcdGrove
end Perennial
