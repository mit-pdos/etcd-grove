/-
`(*DaemonSetsController).deleteDaemonset(...)` (`daemon_controller.go:323`). Lean-first; track C of the DaemonSet run (`notes/k8s-daemonset-run/design.md`, "The handler contract").

The object is a registered DaemonSet or a tombstone of one, gone from the API state
after its version (the event's `goneAfter`): its key (`KeyFunc`), the consistency store's
`Clear(owner, uid)` (fired inside `s1Inv`: the owner with that UID is dead, its record no longer
guards any sync; `sceneOk` makes the case dead in the scenario), the expectations'
`DeleteExpectations(key)`, the key added to the queue.
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

/-- **`dsc.deleteDaemonset(...)`**: see the file header; the thread token back. -/
abbrev DaemonSetsController.deleteDaemonset.spec : Prop :=
  ∀ [workqueue.QItem (GF := GF) GoString go.string] (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (logger : github_com.go_logr.logr.Logger) (x : GoInterface),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ evFacts γa .daemonSets c.dsI.γi (.delete x) }}
    (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"deleteDaemonset")) (Val #logger)) (Val #x))
  {{ RET #(); threadTok }}

end spec

end dsctl
end EtcdGrove
end Perennial
