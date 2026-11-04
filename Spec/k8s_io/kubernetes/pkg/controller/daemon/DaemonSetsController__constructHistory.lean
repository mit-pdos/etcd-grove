/-
`(*DaemonSetsController).constructHistory(ctx, ds)` (`update.go:299`): the DaemonSet's revisions
(`controlledHistories`), the hash label added where missing (an `Update`), split into current
(`Match`) and old; the current one deduplicated (`dedupCurHistories`) and its revision raised if
needed (an `Update`), or created (`snapshot`). Lean-first; Stage 3, track B.

Under `sceneOk` the cache holds at most one revision of the DaemonSet, the one it made
(`crsOfDs`), which has the hash label and matches: so no label write (whose map may be `nil`), no
deduplication's pod `Patch` (the model has none). The current revision's hash label is the
DaemonSet's hash (`crOf`), what the sync labels its pods with.
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

/-- **`dsc.constructHistory(ctx, ds)`**: see the file header. -/
abbrev DaemonSetsController.constructHistory.spec : Prop :=
∀ (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ ∗ dsArg γa c ds o d }}
    (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"constructHistory")) (Val #ctx)) (Val #ds))
  {{ (cur : Loc) (old : GoSlice) (err : GoInterface), RET (PairV (PairV #cur #old) #err);
      threadTok ∗ fmt.argOk err ∗
      (⌜err ≠ interface.nil⌝ ∨ ⌜err = interface.nil⌝ ∗
        (∃ r, □ crAt cur DFrac.discard r ∗ ⌜crOf d r⌝) ∗ ∃ rs, crsAt old (DFrac.own 1) rs) }}

end spec

end dsctl
end EtcdGrove
end Perennial
