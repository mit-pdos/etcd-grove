/-
`(*metav1.ObjectMeta).GetLabels` (`k8s.io/apimachinery/pkg/apis/meta/v1/meta.go`): returns the field `Labels`. Lean-first
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]

/-- `meta.GetLabels()`: the field `Labels`. -/
abbrev ObjectMeta.GetLabels.spec : Prop :=
  ∀ (l : Loc) (v : _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta) (dq : DFrac),
  {{ (l ↦{dq} v : IProp GF) }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta.ty @!! go!"GetLabels")) (Val #()))
  {{ RET #v.Labels'; l ↦{dq} v }}

end spec

end metav1
end EtcdGrove
end Perennial
