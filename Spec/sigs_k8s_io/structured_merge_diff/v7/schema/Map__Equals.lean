/-
`(*Map).Equals(b)`: whether two map types are equal: element type (`TypeRef.Equals`),
relationship, fields in order (`StructField.Equals`), unions. On a shared schema's map types
(`isMapRep`: no unions, the nil slice, so `Union.Equals` is never called) it decides the equality of
their abstract descriptions; the lazy `FindField` indexes are not compared.

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
abbrev schema.Map.Equals.spec : Prop :=
  ∀ (a b : Loc) (fs fs' : List (GoString × TypeRef)) (e e' : Option TypeRef) (rel rel' : ElemRel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.schema ∗ isMapRep a fs e rel ∗ isMapRep b fs' e' rel' }}
    (App (Val (a @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.Map.ty @!! go!"Equals")) (Val #b))
  {{ (r : Bool), RET #r; ⌜r = true ↔ (fs, e, rel) = (fs', e', rel')⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
