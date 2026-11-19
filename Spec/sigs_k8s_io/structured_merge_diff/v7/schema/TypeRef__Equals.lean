/-
`(*TypeRef).Equals(b)`: whether two type references are equal: the same name (or both unnamed),
the same `ElementRelationship` pointer, the same `Nullable`, equal inlined atoms. On references in
the scope (`isTypeRefOpt`: named without override, or the empty `TypeRef`; inlined atoms zero) it
decides the equality of the abstract references (`Option TypeRef`: name and nullability).

The receiver and argument are pointers into whatever holds the references (a `TypedValue`'s field,
a local copy, a schema's `Map.ElementType`, a `StructField.Type`): taken at any fractions and given
back.

A cross-package spec (its callers: `typed`'s `TypedValue.Compare` and `merge`, which check both
objects have one type; `Map.Equals`, `List.Equals`, `StructField.Equals`). Draft (2026-11-19,
notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : schema.Assumptions]

/-- See the file header. -/
abbrev schema.TypeRef.Equals.spec : Prop :=
  ∀ (a b : Loc) (dq1 dq2 : DFrac) (ta tb : schema.TypeRef) (oa ob : Option TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.schema ∗ a ↦{dq1} ta ∗ isTypeRefOpt ta oa ∗ b ↦{dq2} tb ∗ isTypeRefOpt tb ob }}
    (App (Val (a @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.TypeRef.ty @!! go!"Equals")) (Val #b))
  {{ (r : Bool), RET #r; a ↦{dq1} ta ∗ b ↦{dq2} tb ∗ ⌜r = true ↔ oa = ob⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
