/-
`(*ControllerExpectations).GetExpectations(controllerKey)` (`controller_utils.go:174`): the
store's `GetByKey`, and the record asserted to be a `*ControlleeExpectations`. Lean-first; phase 5
of `notes/k8s-daemonset-plan.md`.
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

/-- **`r.GetExpectations(key)`**: the key's record `e` and `true` (a `*ControlleeExpectations`),
or `nil` and `false`; never an error (the store's `GetByKey` returns none). Needs a reader slot,
given back. -/
abbrev ControllerExpectations.GetExpectations.spec : Prop :=
  ∀ (r : Loc) (γe : ExpNames) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ isExp r γe ∗
      expReader γe }}
    (App (Val (r @!! go.GoType.PointerType ControllerExpectations.ty @!! go!"GetExpectations"))
      (Val #key))
  {{ (e : Loc) (ok : Bool), RET (PairV (PairV #e #ok) #(interface.nil : GoInterface));
      expReader γe ∗ (if ok then ∃ k, isCE e k else ⌜e = null⌝) }}

end spec

end dsctl
end EtcdGrove
end Perennial
