/-
`(*DaemonSetsController).getDaemonSetsForHistory(...)` (`daemon_controller.go:458`): the DaemonSets whose
selector selects the controller revision's labels (`dsLister.GetHistoryDaemonSets`), `nil` on an error. Lean-first; track C.
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

/-- **`dsc.getDaemonSetsForHistory(...)`**: a slice of cached DaemonSets (`dssSeen`). -/
abbrev DaemonSetsController.getDaemonSetsForHistory.spec : Prop :=
  ∀  (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (logger : github_com.go_logr.logr.Logger) (history : Loc) (x : kd.apps.ControllerRevision),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ isDsc dsc c cfg γa F ∗ threadTok ∗ □ crAt history DFrac.discard x }}
    (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"getDaemonSetsForHistory")) (Val #logger)) (Val #history))
  {{ (sl : GoSlice), RET #sl; threadTok ∗ dssSeen γa sl }}

end spec

end dsctl
end EtcdGrove
end Perennial
