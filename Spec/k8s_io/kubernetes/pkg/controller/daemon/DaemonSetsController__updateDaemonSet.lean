/-
`(*DaemonSetsController).updateDaemonSet(ctx, ds, nodeList, hash, key, old)`
(`daemon_controller.go:973`): `manage`, then, if the expectations are satisfied, the rolling update
(`rollingUpdate` for the `RollingUpdate` strategy), then `cleanupHistory`. Lean-first; Stage 3,
track B. A glue function: the ready token to `manage`, the sync token through the rest.
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

/-- **`dsc.updateDaemonSet(ctx, ds, nodeList, hash, key, old)`**: see the file header. -/
abbrev DaemonSetsController.updateDaemonSet.spec : Prop :=
∀ [workqueue.QItem (GF := GF) GoString go.string] (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet) (nl : GoSlice) (ns : List kd.core.Node) (hash key : GoString)
    (old : GoSlice) (rs : List kd.apps.ControllerRevision) (L : Nat),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ ∗ dsArg γa ds o d ∗ nodesAt nl ns ∗
      ⌜(ns.map (fun n => n.ObjectMeta'.Name')).Nodup ∧ hash = dsHash d⌝ ∗
      crsAt old (DFrac.own 1) rs ∗ readyTok γ c o L }}
    (App (App (App (App (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"updateDaemonSet")) (Val #ctx)) (Val #ds)) (Val #nl)) (Val #hash)) (Val #key)) (Val #old))
  {{ (err : GoInterface), RET #err; threadTok ∗ syncTok γ c o ∗ fmt.argOk err }}

end spec

end dsctl
end EtcdGrove
end Perennial
