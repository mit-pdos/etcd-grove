/-
`(*Schema).Resolve(tr)`: the atom a type reference denotes: for a named reference, the named
type's atom (`S.resolveRef (some t) = S.find t.name`; an unknown name gives the zero atom and
`false`); for the empty `TypeRef` (`schema.TypeRef{}`, which the `typed` walkers and `fieldpath`
resolve for a key without a type), the zero atom and `true`. The returned `schema.Atom` is a copy
of the type definition's: its pointers are the schema's own, so a map type's `FindField` index
comes with it (`isAtomOpt`).

In the scope no reference has an element-relationship override (`isTypeRefOpt`:
`ElementRelationship` nil), so `Resolve` goes straight to `resolveNoOverrides` and never takes the
schema's `lock` or touches its `resolvedTypes` cache: the persistent `isSchema` suffices, and
concurrent callers are covered. The override path (a copy of the map or list type with the
override, cached under the lock) is out of scope (`notes/smd-plan.md`, "Scope", (R)).

A cross-package spec (its callers: `typed`'s `resolveSchema`, the walkers' `compare`/`merge`/
`reconcile`, `getAssociativeKeyDefault`; `fieldpath`'s `EnsureNamedFieldsAreMembers`). The
names-distinct premise comes from `Schema.WF` (`Schema.WF_types_nodup`, `schema/Laws.lean`).
Draft (2026-11-19, notes/smd-plan.md).
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
abbrev schema.Schema.Resolve.spec : Prop :=
  ∀ (sc : Loc) (S : Schema) (tr : schema.TypeRef) (ot : Option TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.schema ∗ isSchema sc S ∗ isTypeRefOpt tr ot ∗ ⌜(S.types.map (·.1)).Nodup⌝ }}
    (App (Val (sc @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.Schema.ty @!! go!"Resolve")) (Val #tr))
  {{ (a : schema.Atom) (ok : Bool), RET (PairV #a #ok);
      ⌜ok = S.resolvesRef ot⌝ ∗ isAtomOpt a (S.resolveRef ot) }}

end spec

end smd
end EtcdGrove
end Perennial
