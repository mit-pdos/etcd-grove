/-
`NodeShouldRunDaemonPod(logger, node, ds)` (`daemon_controller.go:1392`): `nodeShouldRunDaemonPod`
with the DaemonSet's tolerations (`daemonPodTolerations`) and its template's required node
affinity. Lean-first; track C of the DaemonSet run (`syncNodeUpdate` calls it).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.LifeDefs

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel informer informers cache workqueue k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

/-- **`NodeShouldRunDaemonPod(logger, node, ds)`**: two booleans. -/
abbrev NodeShouldRunDaemonPod.spec : Prop :=
  ∀ (logger : github_com.go_logr.logr.Logger) (node : Loc) (n : kd.core.Node) (ds : Loc) (d : kd.apps.DaemonSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ □ nodeAt node DFrac.discard n ∗ □ dsAt ds DFrac.discard d }}
    (App (App (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.NodeShouldRunDaemonPod))
      (Val #logger)) (Val #node)) (Val #ds))
  {{ (b1 b2 : Bool), RET (PairV #b1 #b2); True }}

end spec

end dsctl
end EtcdGrove
end Perennial
