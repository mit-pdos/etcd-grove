/-
`failedPodsBackoffKey(ds, nodeName)` (`daemon_controller.go:1482`): a string key. Lean-first;
Stage 3, track B.
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
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

/-- **`failedPodsBackoffKey(ds, n)`**: some string. -/
abbrev failedPodsBackoffKey.spec : Prop :=
  ∀ (ds : Loc) (d : kd.apps.DaemonSet) (n : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ □ dsAt ds DFrac.discard d }}
    (App (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.failedPodsBackoffKey)) (Val #ds)) (Val #n))
  {{ (s : GoString), RET #s; True }}

end spec

end dsctl
end EtcdGrove
end Perennial
