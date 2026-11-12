/-
`meta.Accessor(obj)` (`k8s.io/apimachinery/pkg/api/meta/meta.go:96`) of an object whose dynamic
type is a `metav1.Object`: the type switch's first case returns the object itself, as a
`metav1.Object`, and `nil`. It reads nothing. Proved from the translated body
(`Proof/k8s_io/apimachinery/pkg/api/meta/Accessor.lean`; stage 7b of `notes/k8s-etcd3-plan.md`,
D3: before, a named hypothesis of the DaemonSet track for its four API pointer types).

Callers: `storage.Preconditions.Check` (any `metav1.Object`), the pod control's create
(`*apps.DaemonSet`).
-/
module

public import Proof.k8s_io.apimachinery.pkg.api.meta.Init

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

/-- **`meta.Accessor(x)`** of an `x` whose dynamic type is in `metav1.Object`'s type set: `x`
itself and `nil`. -/
abbrev Accessor.spec : Prop :=
  ∀ (ii : GoInterfaceOk),
    go.typeSetContains ii.ty k8s_io.apimachinery.pkg.apis.«meta».v1.Object.ty = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».Accessor)) (Val #(GoInterface.ok ii)))
  {{ RET (PairV #(GoInterface.ok ii : k8s_io.apimachinery.pkg.apis.«meta».v1.Object)
      #(interface.nil : GoInterface)); True }}

end spec

end apimeta
end EtcdGrove
end Perennial
