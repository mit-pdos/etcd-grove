/-
`(*DaemonSetsController).addPod(...)` (`daemon_controller.go:588`). Lean-first; track C of the DaemonSet run (`notes/k8s-daemonset-run/design.md`, "The handler contract").

The added pod is registered (the event's facts): if being deleted, `deletePod`; with a
controller reference resolving to a DaemonSet, the expectations' `CreationObserved(key)` and the
DaemonSet enqueued; an orphan's matching DaemonSets (`getDaemonSetsForPod`) enqueued.
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

/-- **`dsc.addPod(...)`**: see the file header; the thread token back. -/
abbrev DaemonSetsController.addPod.spec : Prop :=
  ∀ [workqueue.QItem (GF := GF) GoString go.string] (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (logger : github_com.go_logr.logr.Logger) (x : GoInterface) (b : Bool),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ evFacts γa .pods c.podI.γi (.add x b) }}
    (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"addPod")) (Val #logger)) (Val #x))
  {{ RET #(); threadTok }}

end spec

end dsctl
end EtcdGrove
end Perennial
