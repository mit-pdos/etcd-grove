/-
`typed.mapValue(a, val)` (internal): the map view of a value: an error for nil, nil for `null`,
the view of a map (`isMapV`), an error for any other kind. The value is lent (any share).

Prove phase (2026-11-19, the coordinator's decision): the value is `null` or a map (the premise,
as `derefMap`'s, its callers'), so neither `fmt.Errorf` branch is reached and no `fmt` spec is
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
abbrev typed.mapValue.spec : Prop :=
  ∀ (a : value.Allocator) (v : value.Value) (dq : DFrac) (o : Option UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isValO v dq o ∗
      ⌜o = some .null ∨ (mapOfO o).isSome⌝ }}
    (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mapValue)) (Val #a)) (Val #v))
  {{ (m : value.Map) (err : GoInterface), RET (PairV #m #err); isValO v dq o ∗
      isMapO m (mapOfO o) ∗ ⌜err = interface.nil ↔ (o = some .null ∨ (mapOfO o).isSome)⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
