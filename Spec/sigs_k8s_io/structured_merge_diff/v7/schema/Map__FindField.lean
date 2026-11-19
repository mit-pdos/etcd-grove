/-
`(*Map).FindField(name)`: the declared field `name` of a map type, from the map's lazily built
index (a `sync.Once` and an `atomic.Pointer`, as `Schema.FindNamedType`'s: part of the persistent
`isMapRep`). The index maps a name to the last field of that name; the premise that the field names
are distinct (implied by `Schema.WF` for every map type of the schema) makes it the declared one.
On a miss Go returns the zero `StructField`.

A cross-package spec (its callers: the `typed` walkers on a map's keys, `fieldpath`'s
`EnsureNamedFieldsAreMembers`). Draft (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Defs

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
variable [package_sem : schema.Assumptions]

/-- See the file header. -/
abbrev schema.Map.FindField.spec : Prop :=
  ∀ (m : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel) (n : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.schema ∗ isMapRep m fs e rel ∗ ⌜(fs.map (·.1)).Nodup⌝ }}
    (App (Val (m @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.Map.ty @!! go!"FindField")) (Val #n))
  {{ (sf : schema.StructField) (ok : Bool), RET (PairV #sf #ok);
      match lookupKV n fs with
      | some t => iprop(⌜ok = true⌝ ∗ isStructField sf (n, t))
      | none => iprop(⌜ok = false ∧ sf = zero_val schema.StructField⌝) }}

end spec

end smd
end EtcdGrove
end Perennial
