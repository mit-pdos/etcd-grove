/-
`(*Atom).Equals(b)`: whether two atoms are equal: the same kinds set, then the scalars' names, the
lists (`List.Equals`) or the maps (`Map.Equals`). On atoms in the scope (`isAtomOpt`: a shared
schema's atom, or the zero atom) it decides the equality of the abstract atoms: the zero atom
(`none`) equals only itself, and two schema atoms are equal exactly when they are the same `Atom`
(scalar kind; list element type, relationship and keys; map fields in order, element type and
relationship). The map types' lazy `FindField` indexes are not compared.

The receiver and argument are pointers to atom values (the `typed` walkers' deduced atoms, local
variables; a `TypeRef`'s `Inlined` field): taken at any fractions and given back.

A cross-package spec (its callers: `typed`'s `compareWalker.compare` and `mergingWalker.merge`,
`alhs.Equals(&arhs)`; `TypeRef.Equals`). Draft (2026-11-19, notes/smd-plan.md).
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
abbrev schema.Atom.Equals.spec : Prop :=
  ∀ (a b : Loc) (dq1 dq2 : DFrac) (va vb : schema.Atom) (oA oB : Option Atom),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.schema ∗ a ↦{dq1} va ∗ isAtomOpt va oA ∗ b ↦{dq2} vb ∗ isAtomOpt vb oB }}
    (App (Val (a @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.Atom.ty @!! go!"Equals")) (Val #b))
  {{ (r : Bool), RET #r; a ↦{dq1} va ∗ b ↦{dq2} vb ∗ ⌜r = true ↔ oA = oB⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
