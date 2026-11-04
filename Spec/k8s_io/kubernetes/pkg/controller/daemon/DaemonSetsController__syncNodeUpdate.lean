/-
`(*DaemonSetsController).syncNodeUpdate(ctx, nodeName)` (`daemon_controller.go:1534`): the node
from the lister (not found: `nil`); every DaemonSet from the lister; the node's pods (the pod
indexer's `spec.nodeName` index); the pods grouped by their DaemonSet controller's key; each
DaemonSet whose placement on the node changed (`NodeShouldRunDaemonPod` against the pods there,
or a misscheduled count) enqueued. Reads only: errors are formatted by the caller (`%w`).
Lean-first; track C.
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

/-- **`dsc.syncNodeUpdate(ctx, nodeName)`**: reads and enqueues; an error the worker can format. -/
abbrev DaemonSetsController.syncNodeUpdate.spec : Prop :=
  ∀ [workqueue.QItem (GF := GF) GoString go.string] (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (nodeName : GoString),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ }}
    (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"syncNodeUpdate")) (Val #ctx)) (Val #nodeName))
  {{ (err : GoInterface), RET #err; threadTok ∗ fmt.argOk err }}

end spec

end dsctl
end EtcdGrove
end Perennial
