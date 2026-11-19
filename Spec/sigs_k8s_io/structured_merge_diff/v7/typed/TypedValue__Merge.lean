/-
`TypedValue.Merge(pso)` (value receiver): `pso` (the configuration) merged into the receiver (the
live object), both of one schema and one type: the right side's scalars and atomic values win,
maps merge per key, associative lists per item key in `mergeKeys` order (`merge`). The result is
a fresh typed value of the same schema and type, which conforms (`merge_conforms.law`). No error
in the scope (one schema pointer, one type, conforming values: `merge`'s checks and the walker's
errors cannot happen).

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
abbrev typed.TypedValue.Merge.spec : Prop :=
  ∀ (tv : _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue) (q sc : Loc) (S : Schema) (t : TypeRef) (l r : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isTVv tv sc S t l ∗ isTV q sc S t r }}
    (App (Val (tv @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue.ty @!! go!"Merge")) (Val #q))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      ⌜err = interface.nil⌝ ∗ isTV p sc S t (merge S t l r) }}

end spec

end smd
end EtcdGrove
end Perennial
