/-
`meta.Accessor(obj)` (`k8s.io/apimachinery/pkg/api/meta/meta.go:96`, names-only) of a
`*controller.ControlleeExpectations`. **A named hypothesis, boundary pending approval** (the
controller expectations' store calls it in `Add` and `Delete`, `threadSafeMap`'s resource-version
bookkeeping; phase 5 of `notes/k8s-daemonset-plan.md`).

What the code does: `*ControlleeExpectations` implements neither `metav1.Object` nor
`metav1.ObjectMetaAccessor` (it has no methods but `Add`, `Fulfilled`, `GetExpectations`,
`MarshalLog`, `isExpired`), so the type switch's `default` case returns `nil` and
`errNotObject`, a `fmt.Errorf` error (non-`nil`). It reads nothing.
-/
module

public import Proof.k8s_io.apimachinery.pkg.api.meta.Init
public import GeneratedProof.k8s_io.kubernetes.pkg.controller

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimeta

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]

/-- **`meta.Accessor(e)`** of a `*ControlleeExpectations` `e`: some non-`nil` error. -/
abbrev Accessor_ControlleeExpectations.spec : Prop :=
  ∀ (e : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».Accessor))
      (Val #(interface.mkOk
        (go.GoType.PointerType k8s_io.kubernetes.pkg.controller.ControlleeExpectations.ty) #e :
          GoInterface)))
  {{ (m err : GoInterface), RET (PairV #m #err); ⌜err ≠ interface.nil⌝ }}

end spec

end apimeta
end EtcdGrove
end Perennial
