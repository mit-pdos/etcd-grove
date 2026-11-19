/-
`(*List).Equals(b)`: whether two list types are equal: element type (`TypeRef.Equals`),
relationship, and key field names in order. On a shared schema's list types (`isListRep`) it
decides the equality of their abstract descriptions.

Internal to `schema` (its caller is `Atom.Equals`). Draft (2026-11-19, notes/smd-plan.md).
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
abbrev schema.List.Equals.spec : Prop :=
  ∀ (a b : Loc) (e e' : TypeRef) (rel rel' : ElemRel) (ks ks' : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.schema ∗ isListRep a e rel ks ∗ isListRep b e' rel' ks' }}
    (App (Val (a @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.List'.ty @!! go!"Equals")) (Val #b))
  {{ (r : Bool), RET #r; ⌜r = true ↔ (e, rel, ks) = (e', rel', ks')⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
