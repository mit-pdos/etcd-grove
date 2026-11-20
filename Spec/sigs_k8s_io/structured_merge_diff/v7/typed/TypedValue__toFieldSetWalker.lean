/-
`TypedValue.toFieldSetWalker()` (value receiver, internal): a field-set walker from `tPool`
(`typedPools`) set to the typed value's value, schema and type, at the root (path `[]`), with a
fresh empty set (`&fieldpath.Set{}`, owned) and a fresh allocator.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

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
variable [package_sem : typed.Assumptions]

/-- See the file header. -/
abbrev typed.TypedValue.toFieldSetWalker.spec : Prop :=
  ∀ (tv : _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue) (sc : Loc) (S : Schema) (t : TypeRef) (x : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isTVv tv sc S t x }}
    (App (Val (tv @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue.ty @!! go!"toFieldSetWalker")) (Val #()))
  {{ (w : Loc), RET #w; ∃ (s : Loc) (a : value.Allocator) (sp : Loc), twOwn w sc S ⟨tv.value', t, [], a⟩ s PathSet.empty sp }}

end spec

end smd
end EtcdGrove
end Perennial
