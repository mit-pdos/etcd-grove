/-
`getUnscheduledPodsWithoutNode(runningNodesList, nodeToDaemonPods)` (`daemon_controller.go:1488`):
the names of the map's pods on nodes not in the list that no node is bound to. Lean-first; Stage 3,
track B. Any names (pods to delete).
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

/-- **`getUnscheduledPodsWithoutNode(nl, m)`**: a fresh slice of names; the map comes back. -/
abbrev getUnscheduledPodsWithoutNode.spec : Prop :=
  ∀ (nl : GoSlice) (ns : List kd.core.Node) (m : GoMap) (Mp : GMap GoString (List kd.core.Pod)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ nodesAt nl ns ∗ podMapAt m Mp }}
    (App (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.getUnscheduledPodsWithoutNode)) (Val #nl)) (Val #m))
  {{ (sl : GoSlice) (names : List GoString), RET #sl; nodesAt nl ns ∗ podMapAt m Mp ∗ sl ↦* names }}

end spec

end dsctl
end EtcdGrove
end Perennial
