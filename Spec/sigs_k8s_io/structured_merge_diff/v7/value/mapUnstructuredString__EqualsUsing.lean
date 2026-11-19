/-
`mapUnstructuredString.EqualsUsing(a, other)`: whether the two maps have the same entries
(canonical, so `=`); `other` non-nil (a nil `Map` would panic at `other.Length()`).

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
abbrev value.mapUnstructuredString.EqualsUsing.spec : Prop :=
  ∀ (m : GoMap) (kvs kvs' : List (GoString × UVal)) (al : value.Allocator) (o : value.Map),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isMapV (interface.mkOk value.mapUnstructuredString.ty #m) kvs ∗ isMapV o kvs' ∗ isAlloc al }}
    (App (App (Val (m @!! value.mapUnstructuredString.ty @!! go!"EqualsUsing")) (Val #al)) (Val #o))
  {{ (r : Bool), RET #r; isAlloc al ∗ ⌜r = true ↔ kvs = kvs'⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
