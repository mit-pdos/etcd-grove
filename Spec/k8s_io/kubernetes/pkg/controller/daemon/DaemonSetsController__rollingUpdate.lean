/-
`(*DaemonSetsController).rollingUpdate(ctx, ds, nodeList, hash)` (`update.go:46`): the pods by
node, the surge and unavailability allowances (`updatedDesiredNodeCounts`), then old pods to
delete (and, when surging, nodes to create a new pod on next to an old one), `syncNodes`.
Lean-first; Stage 3, track B.

**What S1 needs**: no create. Every pod of the map is the DaemonSet's (`podsView`'s `ctlBy`, then
`uidInj`) and carries its hash label (`podOf`), so
`findUpdatedPodsOnNode` finds no old pod on any node and both branches leave the nodes to create
empty, whatever `MaxSurge` holds (gap C5: the model's defaulted `MaxSurge` is opaque).
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

/-- **`dsc.rollingUpdate(ctx, ds, nodeList, hash)`**: see the file header. -/
abbrev DaemonSetsController.rollingUpdate.spec : Prop :=
∀ (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet) (nl : GoSlice) (ns : List kd.core.Node) (hash : GoString),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ ∗ dsArg γa c ds o d ∗ nodesAt nl ns ∗
      ⌜hash = dsHash d⌝ ∗ syncTok γ c o }}
    (App (App (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"rollingUpdate")) (Val #ctx)) (Val #ds)) (Val #nl)) (Val #hash))
  {{ (err : GoInterface), RET #err; threadTok ∗ syncTok γ c o ∗ fmt.argOk err }}

end spec

end dsctl
end EtcdGrove
end Perennial
