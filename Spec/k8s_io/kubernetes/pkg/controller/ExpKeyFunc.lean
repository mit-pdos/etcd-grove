/-
`ExpKeyFunc`'s closure (`controller_utils.go:149`, a package variable's function literal,
`expKeyFn`): on a `*ControlleeExpectations` its key and `nil`. Lean-first; phase 5 of
`notes/k8s-daemonset-plan.md`.

Only the expectations' objects are specified (the error path, `fmt.Errorf` with `%#v` of an
arbitrary object, is never taken by the expectations' store, which only holds
`*ControlleeExpectations`).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]

/-- **`ExpKeyFunc(obj)`** for `obj` a `*ControlleeExpectations` `e`: its key, and `nil`. -/
abbrev ExpKeyFunc.spec : Prop :=
  ∀ (e : Loc) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗
      structFieldRef ControlleeExpectations go!"key" e ↦□ k }}
    (App (Val #(expKeyFn : GoFunc))
      (Val #(interface.mkOk (go.GoType.PointerType ControlleeExpectations.ty) #e : GoInterface)))
  {{ RET (PairV #k #(interface.nil : GoInterface)); True }}

end spec

end dsctl
end EtcdGrove
end Perennial
