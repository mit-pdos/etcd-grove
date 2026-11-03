/-
`controller.RecheckDeletionTimestamp(getObject)` (`controller_ref_manager.go:391`): a closure that
gets the object and fails if it is being deleted. Lean-first; Stage 3, track B. The DaemonSet
controller's ref managers never adopt (`sceneOk`: no orphans), so the closure is never called: the
spec says only that a closure is returned.
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

/-- **`RecheckDeletionTimestamp(f)`**: some function value. -/
abbrev RecheckDeletionTimestamp.spec : Prop :=
  ∀ (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller }}
    (App (Val (@! k8s_io.kubernetes.pkg.controller.RecheckDeletionTimestamp)) (Val #f))
  {{ (h : GoFunc), RET #h; True }}

end spec

end dsctl
end EtcdGrove
end Perennial
