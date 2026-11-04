/-
`(*DaemonSetsController).updateNode(...)` (`daemon_controller.go:748`). Lean-first; track C of the DaemonSet run (`notes/k8s-daemonset-run/design.md`, "The handler contract").

Both registered (`infObj`: the unchecked assertions and the dereferences):
`shouldIgnoreNodeUpdate(*old, *cur)`, else the current node's name added to the node queue.
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

/-- **`dsc.updateNode(...)`**: see the file header; the thread token back. -/
abbrev DaemonSetsController.updateNode.spec : Prop :=
  ∀  (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (logger : github_com.go_logr.logr.Logger) (x1 x2 : GoInterface),
  {{ dscEnv dsc c cfg γa F γ ∗ infObj c.nodeI.γi .nodes x1 ∗ infObj c.nodeI.γi .nodes x2 }}
    (App (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"updateNode")) (Val #logger)) (Val #x1)) (Val #x2))
  {{ RET #(); True }}

end spec

end dsctl
end EtcdGrove
end Perennial
