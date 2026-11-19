/-
`typed.listValue(a, val)` (internal): the list view of a value: nil for `null`, the view of a list
(`isListV`), an error for any other kind. The value is lent (any share); the allocator is not used
by the unstructured implementation (`AsListUsing` ignores it).

Prove phase (2026-11-19, the coordinator's decision): the value is `null` or a list (the premise,
as `derefList`'s, its callers'), so the `fmt.Errorf` branch is not reached and no `fmt` spec is
needed; the error is then nil (the post's iff, kept for the callers).

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
abbrev typed.listValue.spec : Prop :=
  ∀ (a : value.Allocator) (v : value.Value) (dq : DFrac) (x : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isValF v dq x ∗
      ⌜x = .null ∨ (listOfO (some x)).isSome⌝ }}
    (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.listValue)) (Val #a)) (Val #v))
  {{ (l : value.List') (err : GoInterface), RET (PairV #l #err); isValF v dq x ∗
      isListO l (listOfO (some x)) ∗
      ⌜err = interface.nil ↔ (x = .null ∨ (listOfO (some x)).isSome)⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
