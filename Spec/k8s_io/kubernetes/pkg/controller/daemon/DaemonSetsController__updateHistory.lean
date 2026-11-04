/-
`(*DaemonSetsController).updateHistory(...)` (`daemon_controller.go:508`). Lean-first; track C of the DaemonSet run (`notes/k8s-daemonset-run/design.md`, "The handler contract").

Both versions registered (the event's facts): unchanged version, nothing; a changed
controller reference's old DaemonSet enqueued; the current one's, or an orphan's matching
DaemonSets on a label or reference change, enqueued.
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

/-- **`dsc.updateHistory(...)`**: see the file header; the thread token back. -/
abbrev DaemonSetsController.updateHistory.spec : Prop :=
  ∀ [workqueue.QItem (GF := GF) GoString go.string] (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (logger : github_com.go_logr.logr.Logger) (x1 x2 : GoInterface),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ evFacts γa .revisions c.crI.γi (.update x1 x2) }}
    (App (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"updateHistory")) (Val #logger)) (Val #x1)) (Val #x2))
  {{ RET #(); threadTok }}

end spec

end dsctl
end EtcdGrove
end Perennial
