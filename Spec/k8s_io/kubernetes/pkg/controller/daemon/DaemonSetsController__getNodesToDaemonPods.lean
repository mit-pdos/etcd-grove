/-
`(*DaemonSetsController).getNodesToDaemonPods(ctx, ds, includeDeletedTerminal)`
(`daemon_controller.go:796`): the DaemonSet's pods (`getDaemonPods`) grouped by target node
(`util.GetTargetNodeName`; a pod whose node cannot be read is skipped, and, unless
`includeDeletedTerminal`, a terminal pod being deleted). Lean-first; Stage 3, track B.

The map's view (`podsView`): at a version at least the bound `L` the caller knows, every pod of
the DaemonSet targeting a node is in the map under it (no pod is terminal or being deleted:
`sceneOk`), and every pod in the map is the DaemonSet's (`ctlBy`: `ClaimPods` keeps only those)
and a logged one.
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

/-- **`dsc.getNodesToDaemonPods(ctx, ds, b)`**: see the file header. -/
abbrev DaemonSetsController.getNodesToDaemonPods.spec : Prop :=
∀ (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet) (b : Bool) (L : Nat),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ ∗ dsArg γa c ds o d ∗
      informer.infRvLb c.podI.γi L }}
    (App (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"getNodesToDaemonPods")) (Val #ctx)) (Val #ds)) (Val #b))
  {{ (m : GoMap) (err : GoInterface), RET (PairV #m #err); threadTok ∗ fmt.argOk err ∗
      (⌜err ≠ interface.nil⌝ ∨ ⌜err = interface.nil⌝ ∗ ∃ Mp, podMapAt m Mp ∗
        podsView γa d.ObjectMeta'.UID' L Mp) }}

end spec

end dsctl
end EtcdGrove
end Perennial
