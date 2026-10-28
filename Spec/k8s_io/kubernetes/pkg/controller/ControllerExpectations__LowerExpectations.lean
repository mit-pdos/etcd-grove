/-
`(*ControllerExpectations).LowerExpectations(logger, controllerKey, add, del)`
(`controller_utils.go:254`): the key's record's counters, if any, decremented. Lean-first; phase 5 of
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

/-- **`r.LowerExpectations(logger, key, add, del)`** returns. Needs a reader slot, given back. -/
abbrev ControllerExpectations.LowerExpectations.spec : Prop :=
  ∀ (r : Loc) (γe : ExpNames) (logger : github_com.go_logr.logr.Logger) (key : GoString) (add del : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ isExp r γe ∗
      expReader γe }}
    (App (App (App (App (Val (r @!! go.GoType.PointerType ControllerExpectations.ty @!!
      go!"LowerExpectations")) (Val #logger)) (Val #key)) (Val #add)) (Val #del))
  {{ RET #(); expReader γe }}

end spec

end dsctl
end EtcdGrove
end Perennial
