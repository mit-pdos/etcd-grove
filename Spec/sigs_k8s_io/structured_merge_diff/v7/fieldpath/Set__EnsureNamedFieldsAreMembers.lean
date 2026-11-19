/-
`Set.EnsureNamedFieldsAreMembers(sc, tr)`: the set with every declared field of a map type that
has a path below it made a member (`ensureNamedOpt`; at a named type `ensureNamed S t s`,
`ensureNamed_opt`). The type is optional (`isTypeRefOpt`: the recursion passes the empty
`TypeRef{}` for a child of no declared type, which resolves to the zero atom). Premises: the schema
in scope (`S.WF`: distinct names, so `FindField`'s and `FindNamedType`'s last-wins indexes agree
with `lookupKV`), and the size bound of `make(…, 0, s.Children.Size())` (the model's sum wraps at
`2^63`, `make` panics on a negative capacity; real Go panics on a capacity above its allocation
limit, a margin: a trie sharing children can count that many paths). Recursive with
`SetNodeMap.EnsureNamedFieldsAreMembers`.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`merge`'s pruning).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NamedVocab

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
variable [package_sem : fieldpath.Assumptions]

/-- See the file header. -/
abbrev fieldpath.Set.EnsureNamedFieldsAreMembers.spec : Prop :=
  ∀ (p : Loc) (s : PathSet) (sc : Loc) (S : Schema) (tr : schema.TypeRef) (ty : Option TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p s ∗ isSchema sc S ∗ isTypeRefOpt tr ty ∗ ⌜S.WF ∧ s.CardLt (2 ^ 63)⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"EnsureNamedFieldsAreMembers")) (Val #sc)) (Val #tr))
  {{ (r : Loc), RET #r; isSet r (ensureNamedOpt S ty s) }}

end spec

end smd
end EtcdGrove
end Perennial
