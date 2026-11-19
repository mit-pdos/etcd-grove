/-
`typed.AsTyped(v, s, typeRef)` (no validation options: a `nil` variadic slice): validates `v`'s
unstructured value `x` against the named type `typeRef` of the schema `s` (`ownSchema`, whose lazy
indexes it may build: threaded through), and returns a new `*TypedValue` of `s` holding `x` and
`typeRef` (`asTyped`), or a `nil` one and an error if `x` does not validate.

Premises: `typeRef` is a named type (`NamedType` non-nil: the walkers resolve it in the schema,
whose map types' lazy indexes `ownSchema` owns; an inlined type's would be owned by no one); the
schema's associative lists have distinct key names (`Schema.keysNodup`: `FieldList.Sort`'s
`sort.SliceStable` then has one result).

Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Own

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
variable [package_sem : merge.Assumptions]

/-- See the file header. -/
abbrev typed.AsTyped.spec : Prop :=
  ∀ (v : value.Value) (x : UVal) (sc : Loc) (S : Schema) (tr : schema.TypeRef) (t : TypeRef),
  t.namedType.isSome = true → S.keysNodup = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ ownValue v x ∗ ownSchema sc S ∗ ownTypeRef false tr t }}
    (App (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.AsTyped)) (Val #v)) (Val #sc)) (Val #tr)) (Val #slice.nil))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err); ownSchema sc S ∗
      match asTyped S x t with
      | some tv => iprop(⌜err = interface.nil⌝ ∗ ownTV p sc tv)
      | none => iprop(⌜p = null ∧ err ≠ interface.nil⌝) }}

end spec

end smd
end EtcdGrove
end Perennial
