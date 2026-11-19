/-
`(*StructField).Equals(b)`: whether two struct fields are equal: name, default
(`reflect.DeepEqual`), type (`TypeRef.Equals`). On fields in the scope (`isStructField`: no default, the
nil interface) it decides the equality of the abstract fields (name and type): the defaults are
compared by `reflect.DeepEqual(nil, nil)`, whose trust-boundary spec (`reflect.DeepEqual.specNil`,
an axiom) covers exactly that case, and which returns `true`. A schema with field defaults needs
another `DeepEqual` spec (`notes/smd-plan.md`, "Scope": no field defaults, (R)).

Internal to `schema` (its caller is `Map.Equals`). Draft (2026-11-19, notes/smd-plan.md).
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
abbrev schema.StructField.Equals.spec : Prop :=
  ∀ (a b : Loc) (dq1 dq2 : DFrac) (sa sb : schema.StructField) (f g : GoString × TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.schema ∗ a ↦{dq1} sa ∗ isStructField sa f ∗ b ↦{dq2} sb ∗ isStructField sb g }}
    (App (Val (a @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.StructField.ty @!! go!"Equals")) (Val #b))
  {{ (r : Bool), RET #r; a ↦{dq1} sa ∗ b ↦{dq2} sb ∗ ⌜r = true ↔ f = g⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
