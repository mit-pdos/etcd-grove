/-
`(*DaemonSetsController).enqueue(ds)` (`daemon_controller.go:420`): the DaemonSet's key
(`controller.KeyFunc`) added to the work queue (an error is logged). Lean-first; track C.

The queue's items satisfy `keyCanon` (decision R5): the caller shows the DaemonSet's key is
canonical (every DaemonSet of the API state has a namespace and a name with no `/`, `sceneOk`).
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

/-- **`dsc.enqueue(ds)`**: returns. -/
abbrev DaemonSetsController.enqueue.spec : Prop :=
  ∀ [workqueue.QItem (GF := GF) GoString go.string] (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (ds : Loc) (d : kd.apps.DaemonSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗ isDsc dsc c cfg γa F ∗ □ dsAt ds DFrac.discard d ∗
      ⌜keyCanon (nameKey d.ObjectMeta'.Namespace' d.ObjectMeta'.Name')⌝ }}
    (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"enqueue")) (Val #ds))
  {{ RET #(); True }}

end spec

end dsctl
end EtcdGrove
end Perennial
