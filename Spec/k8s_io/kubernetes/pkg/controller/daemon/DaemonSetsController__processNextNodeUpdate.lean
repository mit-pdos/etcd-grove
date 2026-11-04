/-
`(*DaemonSetsController).processNextNodeUpdate(ctx)` (`daemon_controller.go:1515`): one node
name off the node queue: `Get` (`false` if shutting down), deferred `Done`, `syncNodeUpdate`;
`Forget` on `nil`, else `HandleError` and `AddRateLimited`; `true`. Lean-first; track C.
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

/-- **`dsc.processNextNodeUpdate(ctx)`**: `false` only once the node queue is shutting down. -/
abbrev DaemonSetsController.processNextNodeUpdate.spec : Prop :=
  ∀  (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ }}
    (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"processNextNodeUpdate")) (Val #ctx))
  {{ (b : Bool), RET #b; threadTok ∗ (⌜b = true⌝ ∨ shutdownLb c.γnq.tq) }}

end spec

end dsctl
end EtcdGrove
end Perennial
