/-
`FieldList.Sort()`: sorts the slice in place by name, stably (`sort.SliceStable`; the two-item
case swaps iff the second name is smaller, which is the same). Stated over the `Field` structs
themselves: the caller (a key under construction: `typed`'s
`keyedAssociativeListItemToPathElement`, `fieldpath.KeyByFields`) keeps whatever it knows of
each field's value.

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
abbrev value.FieldList.Sort.spec : Prop :=
  ∀ (f : GoSlice) (fs : List value.Field),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ f ↦* fs }}
    (App (Val (f @!! value.FieldList.ty @!! go!"Sort")) (Val #()))
  {{ RET #(); f ↦* (fs.mergeSort (fun a b => !gsLt b.Name' a.Name')) }}

end spec

end smd
end EtcdGrove
end Perennial
