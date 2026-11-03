/-
`(*DaemonSetsController).getDaemonPods(ctx, ds)` (`daemon_controller.go:764`): the pods the
DaemonSet controls, from the pod indexer (`FilterPodsByOwner`: by the DaemonSet's controller key, and
the namespace's orphans), claimed through a `PodControllerRefManager` (adopting orphans that match,
releasing controlled pods that do not). Lean-first; Stage 3 of the autoverify run, track B.

Under `sceneOk` no pod is an orphan and every pod of the DaemonSet matches its selector, so the
claim neither adopts nor releases (the model has no pod `Patch`): the result is the indexer's
pods of the DaemonSet, at a version at least the bound `L` the caller knows the pod informer has
reached (`podsListView`).
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

/-- **`dsc.getDaemonPods(ctx, ds)`**: see the file header. -/
abbrev DaemonSetsController.getDaemonPods.spec : Prop :=
∀ [workqueue.QItem (GF := GF) GoString go.string] (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet) (L : Nat),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ ∗ dsArg γa ds o d ∗
      informer.infRvLb c.podI.γi L }}
    (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"getDaemonPods")) (Val #ctx)) (Val #ds))
  {{ (pl : GoSlice) (err : GoInterface), RET (PairV #pl #err); threadTok ∗ fmt.argOk err ∗
      (⌜err ≠ interface.nil⌝ ∨ ⌜err = interface.nil⌝ ∗ ∃ ps, podsAt pl (DFrac.own 1) ps ∗
        podsListView γa d.ObjectMeta'.UID' L ps) }}

end spec

end dsctl
end EtcdGrove
end Perennial
