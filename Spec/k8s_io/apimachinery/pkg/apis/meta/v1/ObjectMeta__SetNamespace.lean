/-
`(*metav1.ObjectMeta).SetNamespace` (`k8s.io/apimachinery/pkg/apis/meta/v1/meta.go`): sets the field `Namespace`. Lean-first
(no Rocq counterpart); the model API server's accessors (`examples/k8sdaemonset/apimodel`).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.apis.«meta».v1

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace metav1

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]

/-- `meta.SetNamespace(x)`: sets the field `Namespace`. -/
abbrev ObjectMeta.SetNamespace.spec : Prop :=
  ∀ (l : Loc) (v : _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta) (x : GoString),
  {{ (l ↦ v : IProp GF) }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty @!! go!"SetNamespace")) (Val #x))
  {{ RET #(); l ↦ { v with Namespace' := x } }}

end spec

end metav1
end EtcdGrove
end Perennial
