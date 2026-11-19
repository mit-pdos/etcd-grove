/-
`TypedValue.ToFieldSet()` (value receiver): the fields the value sets (`fieldSet`): every scalar,
atomic list or map, list item, and map entry that is `null`, `{}` or not a declared field. A
fresh set, **owned** (`ownSet`: the walker built it and keeps nothing of it; `ownSet_persist`
makes it an `isSet`). No error in the scope.

Premise (the same temporary limitation as `Compare`'s, local): the value has fewer than
`typedSizeMax` nodes (`fieldSet_card.law`).

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
abbrev typed.TypedValue.ToFieldSet.spec : Prop :=
  ∀ (tv : _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue) (sc : Loc) (S : Schema) (t : TypeRef) (x : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isTVv tv sc S t x ∗ ⌜x.size < typedSizeMax⌝ }}
    (App (Val (tv @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue.ty @!! go!"ToFieldSet")) (Val #()))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      ⌜err = interface.nil⌝ ∗ ownSet s (fieldSet S t x) }}

end spec

end smd
end EtcdGrove
end Perennial
