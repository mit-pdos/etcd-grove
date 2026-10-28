/-
`(*ControllerExpectations).ExpectDeletions(logger, controllerKey, dels)` (`controller_utils.go:249`):
`SetExpectations(logger, controllerKey, 0, dels)`. Lean-first; phase 5 of
`notes/k8s-daemonset-plan.md`.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import Proof.k8s_io.kubernetes.pkg.controller.ExpDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI k8s_io.kubernetes.pkg.controller

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`r.ExpectDeletions(logger, key, dels)`**: `nil`. -/
abbrev ControllerExpectations.ExpectDeletions.spec : Prop :=
  ∀ (r : Loc) (γe : ExpNames) (logger : github_com.go_logr.logr.Logger) (key : GoString) (dels : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ isExp r γe }}
    (App (App (App (Val (r @!! go.GoType.PointerType ControllerExpectations.ty @!!
      go!"ExpectDeletions")) (Val #logger)) (Val #key)) (Val #dels))
  {{ RET #(interface.nil : GoInterface); True }}

end spec

end dsctl
end EtcdGrove
end Perennial
