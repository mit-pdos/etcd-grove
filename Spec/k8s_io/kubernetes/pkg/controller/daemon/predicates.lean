/-
`predicates(logger, node, taints, tolerations, requiredNodeAffinity)`
(`daemon_controller.go:1439`): whether the node fits the required node affinity
(`RequiredNodeAffinity.Match`, gap D2) and whether its `NoExecute`/`NoSchedule` taints are tolerated
(`FindMatchingUntoleratedTaint`). Lean-first; Stage 3, track B. Any two booleans.
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

/-- **`predicates(logger, node, taints, tols, rna)`**: two booleans; the slices come back. -/
abbrev predicates.spec : Prop :=
  ∀ (logger : github_com.go_logr.logr.Logger) (node : Loc) (n : kd.core.Node) (ts : GoSlice)
    (dq : DFrac) (taints : List k8s_io.api.core.v1.Taint) (tl : GoSlice) (dq' : DFrac)
    (tols : List k8s_io.api.core.v1.Toleration)
    (rna : k8s_io.component_helpers.scheduling.corev1.nodeaffinity.RequiredNodeAffinity),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ □ nodeAt node DFrac.discard n ∗
      ts ↦*{dq} taints ∗ tl ↦*{dq'} tols ∗ rnaOk rna }}
    (App (App (App (App (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.predicates)) (Val #logger)) (Val #node)) (Val #ts)) (Val #tl)) (Val #rna))
  {{ (b1 b2 : Bool), RET (PairV #b1 #b2); ts ↦*{dq} taints ∗ tl ↦*{dq'} tols }}

end spec

end dsctl
end EtcdGrove
end Perennial
