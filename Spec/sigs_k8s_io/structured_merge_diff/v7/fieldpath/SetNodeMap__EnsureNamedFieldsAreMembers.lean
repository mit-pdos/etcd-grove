/-
`SetNodeMap.EnsureNamedFieldsAreMembers(sc, tr)`: the children part of
`Set.EnsureNamedFieldsAreMembers`: each child with its own named fields made members, at the
child's type (`childType`). `make(…, 0, s.Size())`: the size premise as there. Internal.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): internal.
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
abbrev fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.spec : Prop :=
  ∀ (l : Loc) (D : PathSet) (sc : Loc) (S : Schema) (tr : schema.TypeRef) (ty : Option TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D ∗ isSchema sc S ∗ isTypeRefOpt tr ty ∗ ⌜S.WF ∧ D.CardLt (2 ^ 63)⌝ }}
    (App (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"EnsureNamedFieldsAreMembers")) (Val #sc)) (Val #tr))
  {{ (r : Loc), RET #r; isNodes r (PathSet.deep (ensureNamedOpt S ty D)) }}

end spec

end smd
end EtcdGrove
end Perennial
