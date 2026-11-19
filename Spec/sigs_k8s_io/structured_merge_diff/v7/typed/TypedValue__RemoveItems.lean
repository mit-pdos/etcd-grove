/-
`TypedValue.RemoveItems(items)` (value receiver): the value without the paths `items` holds
(`removeItems`: a container emptied on the way, or empty, becomes `null`: SSA-01/02), as a fresh
typed value of the same schema and type.

Premise: the result conforms. `RemoveItems` does not ensure it (removing a list item's key field
leaves an item without its key; `removeItems` keeps an emptied item's key only when the key's
paths are not removed): the caller knows its set (`merge`'s `prune` removes sets closed by
`ensureNamed` under `keysWithItems`), and the post's `isTV` carries conformance.

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
abbrev typed.TypedValue.RemoveItems.spec : Prop :=
  ∀ (tv : _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue) (ip sc : Loc) (S : Schema) (t : TypeRef) (x : UVal) (R : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isTVv tv sc S t x ∗ isSet ip R ∗ ⌜conforms S t (removeItems S t x R)⌝ }}
    (App (Val (tv @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue.ty @!! go!"RemoveItems")) (Val #ip))
  {{ (p : Loc), RET #p; isTV p sc S t (removeItems S t x R) }}

end spec

end smd
end EtcdGrove
end Perennial
