/-
`FieldList.Equals(rhs)`: whether the two field lists are equal (names and values, in order).
Called by `fieldpath` (`PathElement.Equals` of key elements).

Lean-first (2026-11-19, notes/smd-plan.md): Draft, the stage's per-package specs of `value`.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

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
variable [package_sem : value.Assumptions]

/-- See the file header. -/
abbrev value.FieldList.Equals.spec : Prop :=
  ∀ (f g : GoSlice) (fl gl : FieldList),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isFieldList f fl ∗ isFieldList g gl }}
    (App (Val (f @!! value.FieldList.ty @!! go!"Equals")) (Val #g))
  {{ (r : Bool), RET #r; ⌜r = true ↔ fl = gl⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
