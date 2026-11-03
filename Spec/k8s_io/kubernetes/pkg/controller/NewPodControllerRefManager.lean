/-
`controller.NewPodControllerRefManager(podControl, controller, selector, controllerKind, canAdopt,
finalizers...)` (`controller_ref_manager.go:148`): a fresh manager holding them. Lean-first; Stage 3,
track B.
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

open Iris Iris.BI apimodel consistency k8s_io.kubernetes.pkg.controller

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]

/-- **A pod ref manager** over the controller object `ctl` and the selector `sel` (owned: its
`canAdoptOnce` is mutable). -/
def podRefMgrAt (m : Loc) (ctl sel : GoInterface) : IProp GF :=
  iprop(∃ v : PodControllerRefManager, m ↦ v ∗
    ⌜v.BaseControllerRefManager'.Controller' = ctl ∧ v.BaseControllerRefManager'.Selector' = sel⌝)

/-- **`NewPodControllerRefManager(...)`**: a fresh manager over `ctl` and `sel`. -/
abbrev NewPodControllerRefManager.spec : Prop :=
  ∀ (pc : PodControlInterface) (ctl sel : GoInterface)
    (kind : k8s_io.apimachinery.pkg.runtime.schema.GroupVersionKind) (ca : GoFunc) (fins : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller }}
    (App (App (App (App (App (App (Val (@! k8s_io.kubernetes.pkg.controller.NewPodControllerRefManager)) (Val #pc)) (Val #ctl)) (Val #sel)) (Val #kind)) (Val #ca)) (Val #fins))
  {{ (m : Loc), RET #m; podRefMgrAt m ctl sel }}

end spec

end dsctl
end EtcdGrove
end Perennial
