/-
`(*DaemonSetsController).cleanupHistory(ctx, ds, old)` (`update.go:356`): delete the oldest old
revisions beyond `RevisionHistoryLimit` (set: `dsWf`) whose hash no live pod carries. Lean-first;
Stage 3, track B. Revision deletes keep `s1Ok` (`sceneOk.crs` is about the logged ones, which a
delete's change keeps).
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

/-- **`dsc.cleanupHistory(ctx, ds, old)`**: see the file header; `old` is sorted in place. -/
abbrev DaemonSetsController.cleanupHistory.spec : Prop :=
∀ [workqueue.QItem (GF := GF) GoString go.string] (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet) (old : GoSlice) (rs : List kd.apps.ControllerRevision),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ ∗ dsArg γa ds o d ∗ crsAt old (DFrac.own 1) rs }}
    (App (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"cleanupHistory")) (Val #ctx)) (Val #ds)) (Val #old))
  {{ (err : GoInterface), RET #err; threadTok ∗ fmt.argOk err ∗
      ∃ rs', crsAt old (DFrac.own 1) rs' }}

end spec

end dsctl
end EtcdGrove
end Perennial
