/-
`shouldIgnoreNodeUpdate(oldNode, curNode)` (`daemon_controller.go:743`): whether the labels
and taints are semantically equal (`apiequality.Semantic.DeepEqual`). Lean-first; track C.
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

/-- **`shouldIgnoreNodeUpdate(*old, *cur)`** of two cached nodes: some boolean. -/
abbrev shouldIgnoreNodeUpdate.spec : Prop :=
  ∀ (o1 o2 : Loc) (n1 n2 : kd.core.Node) (v1 v2 : k8s_io.api.core.v1.Node),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ o1 ↦□ v1 ∗ □ kd.core.Node.own v1 DFrac.discard n1 ∗
      o2 ↦□ v2 ∗ □ kd.core.Node.own v2 DFrac.discard n2 }}
    (App (App (Val (@! k8s_io.kubernetes.pkg.controller.daemon.shouldIgnoreNodeUpdate)) (Val #v1))
      (Val #v2))
  {{ (b : Bool), RET #b; True }}

end spec

end dsctl
end EtcdGrove
end Perennial
