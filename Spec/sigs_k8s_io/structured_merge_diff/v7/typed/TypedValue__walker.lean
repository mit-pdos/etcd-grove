/-
`TypedValue.walker()` (value receiver, internal): a validating walker from `vPool`
(`typedPools`) set to the typed value's value, schema and type, duplicates not allowed, with its
allocator (a fresh one if it had none).

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
abbrev typed.TypedValue.walker.spec : Prop :=
  ∀ (tv : _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue) (S : Schema) (t : TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isTypeRef tv.typeRef' t ∗ isSchema tv.schema' S ∗ ⌜S.WF⌝ }}
    (App (Val (tv @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue.ty @!! go!"walker")) (Val #()))
  {{ (w : Loc), RET #w; ∃ (a : value.Allocator) (sp : Loc), vwOwn w tv.schema' S ⟨tv.value', t, a⟩ sp }}

end spec

end smd
end EtcdGrove
end Perennial
