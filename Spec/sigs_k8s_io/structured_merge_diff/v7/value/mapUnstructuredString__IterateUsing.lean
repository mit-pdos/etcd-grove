/-
`mapUnstructuredString.IterateUsing(a, fn)`: as `Iterate`, the wrapper from `a` (freed at the
end) and the allocator lent to each call (`iterUFnOk`). Called by `typed`
(`validatingObjectWalker.visitMapItems`) and by `value`'s own zips and `EqualsUsing`.

Lean-first (2026-11-19, notes/smd-plan.md): Draft, the stage's per-package specs of `value`.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects

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
abbrev value.mapUnstructuredString.IterateUsing.spec : Prop :=
  ∀ (m : GoMap) (kvs : List (GoString × UVal)) (al : value.Allocator) (fn : GoFunc)
    (I : List GoString → IProp GF) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isMapV (interface.mkOk value.mapUnstructuredString.ty #m) kvs ∗ isAlloc al ∗ iterUFnOk al fn kvs I Q ∗ I [] }}
    (App (App (Val (m @!! value.mapUnstructuredString.ty @!! go!"IterateUsing")) (Val #al)) (Val #fn))
  {{ (r : Bool), RET #r; isAlloc al ∗ mapIterPost false (kvKeys kvs) I Q r }}

end spec

end smd
end EtcdGrove
end Perennial
