/-
`listUnstructured.RangeUsing(a)`: a range before the first item (`EmptyRange`
for an empty list, else one from `a`), owned (internal).

Internal to `value` (PRINCIPLES, "Scope": may mirror its code).

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
abbrev value.listUnstructured.RangeUsing.spec : Prop :=
  ∀ (l : GoSlice) (vs : List UVal) (al : value.Allocator),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isListV (interface.mkOk value.listUnstructured.ty #l) vs ∗ isAlloc al }}
    (App (Val (l @!! value.listUnstructured.ty @!! go!"RangeUsing")) (Val #al))
  {{ (rg : value.ListRange), RET #rg; isAlloc al ∗ ownRange rg vs (-1) }}

end spec

end smd
end EtcdGrove
end Perennial
