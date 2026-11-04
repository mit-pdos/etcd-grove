/-
`(*DaemonSetsController).manage(ctx, ds, nodeList, hash)` (`daemon_controller.go:1003`): the
pods by node (`getNodesToDaemonPods`), for each node the pods to create and delete
(`podsShouldBeOnNode`), the unscheduled pods on missing nodes, then `syncNodes`. Lean-first; Stage 3,
track B.

**The S1 argument.** The caller's ready token at bound `L` (`readyTok`): `getNodesToDaemonPods` at
`L` gives a map whose view shows no pod of the DaemonSet on each node `podsShouldBeOnNode` asks to
create on (`nodesFree`), the nodes distinct (the node list's names are); so `syncNodes` may create.
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

/-- **`dsc.manage(ctx, ds, nodeList, hash)`**: see the file header. -/
abbrev DaemonSetsController.manage.spec : Prop :=
∀ (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet) (nl : GoSlice) (ns : List kd.core.Node) (hash : GoString) (L : Nat),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ ∗ dsArg γa ds o d ∗ nodesAt nl ns ∗
      ⌜(ns.map (fun n => n.ObjectMeta'.Name')).Nodup ∧ hash = dsHash d⌝ ∗ readyTok γ c o L }}
    (App (App (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"manage")) (Val #ctx)) (Val #ds)) (Val #nl)) (Val #hash))
  {{ (err : GoInterface), RET #err; threadTok ∗ syncTok γ c o ∗ fmt.argOk err }}

end spec

end dsctl
end EtcdGrove
end Perennial
