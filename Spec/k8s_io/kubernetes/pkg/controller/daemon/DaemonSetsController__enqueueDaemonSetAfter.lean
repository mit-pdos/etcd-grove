/-
`(*DaemonSetsController).enqueueDaemonSetAfter(obj, after)` (`daemon_controller.go:431`): the
object's key added to the work queue after `after`. Lean-first; track C (`updatePod` calls it with a
DaemonSet).
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

/-- **`dsc.enqueueDaemonSetAfter(ds, after)`**: returns. -/
abbrev DaemonSetsController.enqueueDaemonSetAfter.spec : Prop :=
  ∀ [workqueue.QItem (GF := GF) GoString go.string] (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (ds : Loc) (d : kd.apps.DaemonSet) (after : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ isDsc dsc c cfg γa F ∗ □ dsAt ds DFrac.discard d ∗
      ⌜keyCanon (nameKey d.ObjectMeta'.Namespace' d.ObjectMeta'.Name')⌝ }}
    (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"enqueueDaemonSetAfter"))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.api.apps.v1.DaemonSet.ty) #ds)))
      (Val #after))
  {{ RET #(); True }}

end spec

end dsctl
end EtcdGrove
end Perennial
