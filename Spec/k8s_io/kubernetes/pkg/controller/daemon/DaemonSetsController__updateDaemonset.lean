/-
`(*DaemonSetsController).updateDaemonset(...)` (`daemon_controller.go:302`). Lean-first; track C of the DaemonSet run (`notes/k8s-daemonset-run/design.md`, "The handler contract").

**The parameters are swapped** (the closure passes `(oldObj, newObj)` to `(cur, old)`;
`nonissues/k8s-daemonset-updatedaemonset-swapped-args.md`): the spec names them as the event does,
`x1` the event's old object, `x2` its new one. When the UIDs differ, the code calls
`deleteDaemonset` on a tombstone of `x2` (the newer DaemonSet), clearing its consistency record;
the scenario never deletes a DaemonSet (`sceneOk`: so an update's two versions have one UID, the
branch is dead) and the proof refutes it from `s1Inv`. Then `enqueueDaemonSet(x1)`.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.LifeDefs

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel informer informers cache workqueue k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

/-- **`dsc.updateDaemonset(...)`**: see the file header; the thread token back. -/
abbrev DaemonSetsController.updateDaemonset.spec : Prop :=
  ∀  (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (logger : github_com.go_logr.logr.Logger) (x1 x2 : GoInterface),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ evFacts γa .daemonSets c.dsI.γi (.update x1 x2) }}
    (App (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"updateDaemonset")) (Val #logger)) (Val #x1)) (Val #x2))
  {{ RET #(); threadTok }}

end spec

end dsctl
end EtcdGrove
end Perennial
