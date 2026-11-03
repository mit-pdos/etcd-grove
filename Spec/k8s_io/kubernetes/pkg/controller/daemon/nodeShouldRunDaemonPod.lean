/-
`nodeShouldRunDaemonPod(logger, node, ds, tolerations, requiredNodeAffinity)`
(`daemon_controller.go:1413`): whether the DaemonSet should run (and keep running) a pod on the
node: its name if the template names one, then `predicates` (node affinity, taints). Lean-first;
Stage 3, track B. S1 does not depend on the answer: any two booleans.
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

/-- **`nodeShouldRunDaemonPod(logger, node, ds, tols, rna)`**: two booleans; the tolerations come back. -/
abbrev nodeShouldRunDaemonPod.spec : Prop :=
  ∀ (logger : github_com.go_logr.logr.Logger) (node : Loc) (n : kd.core.Node) (ds : Loc)
    (d : kd.apps.DaemonSet) (tl : GoSlice) (dq : DFrac) (tols : List k8s_io.api.core.v1.Toleration)
    (rna : k8s_io.component_helpers.scheduling.corev1.nodeaffinity.RequiredNodeAffinity),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ □ nodeAt node DFrac.discard n ∗
      □ dsAt ds DFrac.discard d ∗ tl ↦*{dq} tols ∗ rnaOk rna }}
    (App (App (App (App (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.nodeShouldRunDaemonPod)) (Val #logger)) (Val #node)) (Val #ds)) (Val #tl)) (Val #rna))
  {{ (b1 b2 : Bool), RET (PairV #b1 #b2); tl ↦*{dq} tols }}

end spec

end dsctl
end EtcdGrove
end Perennial
