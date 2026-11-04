/-
`(*DaemonSetsController).snapshot(ctx, ds, revision)` (`update.go:528`): create the revision
`ds.Name + "-" + ComputeHash(template, collisionCount)` with the template's patch (`getPatch`) and
labels plus the hash; if it exists already, the existing one when it matches, else (a hash collision)
the collision count bumped (`UpdateStatus`) and an error. Lean-first; Stage 3, track B.

Under `sceneOk` (`crNameInj`: distinct DaemonSets' revision names differ; every revision is its
DaemonSet's, made from its unchanging template) an existing revision of that name matches: no
collision, the count stays `nil`. The result is the revision the controller made for the
DaemonSet (`crOf`).
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

/-- **`dsc.snapshot(ctx, ds, revision)`**: see the file header. -/
abbrev DaemonSetsController.snapshot.spec : Prop :=
∀ (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (ds : Loc) (o : Owner)
    (d : kd.apps.DaemonSet) (rev : w64),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ ∗ dsArg γa c ds o d }}
    (App (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"snapshot")) (Val #ctx)) (Val #ds)) (Val #rev))
  {{ (cur : Loc) (err : GoInterface), RET (PairV #cur #err); threadTok ∗ fmt.argOk err ∗
      (⌜err ≠ interface.nil⌝ ∨ ⌜err = interface.nil⌝ ∗ ∃ r, □ crAt cur DFrac.discard r ∗
        ⌜crOf d r⌝) }}

end spec

end dsctl
end EtcdGrove
end Perennial
