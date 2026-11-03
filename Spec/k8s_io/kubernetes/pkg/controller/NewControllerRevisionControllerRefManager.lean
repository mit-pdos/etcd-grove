/-
`controller.NewControllerRevisionControllerRefManager(crControl, controller, selector,
controllerKind, canAdopt)` (`controller_ref_manager.go:426`): a fresh manager holding them.
Lean-first; Stage 3, track B.
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

/-- **A revision ref manager** over the controller object `ctl` and the selector `sel` (owned). -/
def crRefMgrAt (m : Loc) (ctl sel : GoInterface) : IProp GF :=
  iprop(∃ v : ControllerRevisionControllerRefManager, m ↦ v ∗
    ⌜v.BaseControllerRefManager'.Controller' = ctl ∧ v.BaseControllerRefManager'.Selector' = sel⌝)

/-- **`NewControllerRevisionControllerRefManager(...)`**: a fresh manager over `ctl` and `sel`. -/
abbrev NewControllerRevisionControllerRefManager.spec : Prop :=
  ∀ (crc : ControllerRevisionControlInterface) (ctl sel : GoInterface)
    (kind : k8s_io.apimachinery.pkg.runtime.schema.GroupVersionKind) (ca : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller }}
    (App (App (App (App (App (Val (@! k8s_io.kubernetes.pkg.controller.NewControllerRevisionControllerRefManager)) (Val #crc)) (Val #ctl)) (Val #sel)) (Val #kind)) (Val #ca))
  {{ (m : Loc), RET #m; crRefMgrAt m ctl sel }}

end spec

end dsctl
end EtcdGrove
end Perennial
