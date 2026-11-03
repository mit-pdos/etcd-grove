/-
`(*DaemonSetsController).updateDaemonSetStatus(ctx, ds, nodeList, hash, updateObservedGen)`
(`daemon_controller.go:1211`): the pods by node, the status counters, `storeDaemonSetStatus`; after
a write, the consistency store's `WroteAt(owner, UID, daemonsets, version)`; a requeue after
`MinReadySeconds`. Lean-first; Stage 3, track B.

The `WroteAt` needs the owner's permission (some fraction) and records a DaemonSets version,
which S1's accounting ignores (`recCovers` reads the pods' version only) but `recOk` keeps (the
record's UID is the DaemonSet's).
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

/-- **`dsc.updateDaemonSetStatus(ctx, ds, nl, hash, b)`**: see the file header. -/
abbrev DaemonSetsController.updateDaemonSetStatus.spec : Prop :=
∀ [workqueue.QItem (GF := GF) GoString go.string] (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet) (nl : GoSlice) (ns : List kd.core.Node) (hash : GoString) (b : Bool)
    (q : Qp),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ ∗ dsArg γa ds o d ∗ nodesAt nl ns ∗ ownerTok c o q }}
    (App (App (App (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"updateDaemonSetStatus")) (Val #ctx)) (Val #ds)) (Val #nl)) (Val #hash)) (Val #b))
  {{ (err : GoInterface), RET #err; threadTok ∗ ownerTok c o q ∗ fmt.argOk err }}

end spec

end dsctl
end EtcdGrove
end Perennial
