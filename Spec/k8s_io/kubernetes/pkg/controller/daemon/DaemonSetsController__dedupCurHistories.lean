/-
`(*DaemonSetsController).dedupCurHistories(ctx, ds, curHistories)` (`update.go:409`): the only
current revision; with several, the newest is kept, the pods relabelled with its hash (a pod
`Patch`, which the model lacks) and the others deleted. Lean-first; Stage 3, track B. Scope: one
current revision (what `constructHistory` passes under `sceneOk`); the deduplication is not
specified.
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

/-- **`dsc.dedupCurHistories(ctx, ds, [r])`**: `r`. -/
abbrev DaemonSetsController.dedupCurHistories.spec : Prop :=
∀ (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet) (hl : GoSlice) (dq : DFrac) (rs : List kd.apps.ControllerRevision),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ ∗ dsArg γa c ds o d ∗ crsAt hl dq rs ∗ ⌜rs.length = 1⌝ }}
    (App (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"dedupCurHistories")) (Val #ctx)) (Val #ds)) (Val #hl))
  {{ (cur : Loc) (err : GoInterface), RET (PairV #cur #err); threadTok ∗ crsAt hl dq rs ∗
      ⌜err = interface.nil⌝ ∗ ∃ r, ⌜rs = [r]⌝ ∗ □ crAt cur DFrac.discard r }}

end spec

end dsctl
end EtcdGrove
end Perennial
