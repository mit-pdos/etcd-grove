/-
`PathElement.Equals(rhs)`: whether the two path elements are equal (`FieldList.Equals` on keys,
`value.Equals` on set items: equality in scope, no floats).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed`'s merge walker compares list items' keys).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

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
variable [package_sem : fieldpath.Assumptions]

/-- See the file header. -/
abbrev fieldpath.PathElement.Equals.spec : Prop :=
  ∀ (e e' : fieldpath.PathElement) (a b : PE),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isPE e a ∗ isPE e' b }}
    (App (Val (e @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement.ty @!! go!"Equals")) (Val #e'))
  {{ (r : Bool), RET #r; ⌜r = true ↔ a = b⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
