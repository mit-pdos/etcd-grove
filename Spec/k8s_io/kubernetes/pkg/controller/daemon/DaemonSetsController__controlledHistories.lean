/-
`(*DaemonSetsController).controlledHistories(ctx, ds)` (`update.go:463`): the namespace's
revisions from the lister, claimed through a `ControllerRevisionControllerRefManager` (adopting
orphans that match, releasing controlled ones that do not). Lean-first; Stage 3, track B.

Under `sceneOk` no revision is an orphan and the DaemonSet's match its selector: no adoption or
release (the model has no revision `Patch`); the result is the DaemonSet's revisions in one view of
the cache: at most one, the one it made (`crsOfDs`).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel consistency k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

/-- **`dsc.controlledHistories(ctx, ds)`**: see the file header. -/
abbrev DaemonSetsController.controlledHistories.spec : Prop :=
∀ [workqueue.QItem (GF := GF) GoString go.string] (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ ∗ dsArg γa ds o d }}
    (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"controlledHistories")) (Val #ctx)) (Val #ds))
  {{ (hl : GoSlice) (err : GoInterface), RET (PairV #hl #err); threadTok ∗ fmt.argOk err ∗
      (⌜err ≠ interface.nil⌝ ∨ ⌜err = interface.nil⌝ ∗ ∃ rs, crsAt hl (DFrac.own 1) rs ∗
        ⌜crsOfDs d rs⌝) }}

end spec

end dsctl
end EtcdGrove
end Perennial
