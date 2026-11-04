/-
`(*DaemonSetsController).runWorker(ctx)` (`daemon_controller.go:395`): `processNextWorkItem`
until it returns `false`. Lean-first; track C of the DaemonSet run.
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

/-- **`dsc.runWorker(ctx)`**: returns once the queue is shutting down, the token back. -/
abbrev DaemonSetsController.runWorker.spec : Prop :=
  ∀ [workqueue.QItem (GF := GF) GoString go.string] (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ }}
    (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"runWorker")) (Val #ctx))
  {{ RET #(); threadTok ∗ shutdownLb c.γq.tq }}

end spec

end dsctl
end EtcdGrove
end Perennial
