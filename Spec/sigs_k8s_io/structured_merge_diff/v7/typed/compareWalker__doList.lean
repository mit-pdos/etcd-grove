/-
`compareWalker.doList(t)` (internal; the `atomHandler` method for a list type): an atomic
list, or one empty on both sides, is a leaf (`doLeaf`); otherwise the items are
compared (`visitListItems`). Adds `cmpBelow` (the node's own addition or removal is
`compare`'s, after); `inLeaf` ends as whether the node is a leaf.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

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
variable [package_sem : typed.Assumptions]

/-- See the file header. -/
abbrev typed.compareWalker.doList.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (dql dqr : DFrac) (l r : Option UVal) (tp : Loc) (e : TypeRef) (rel : ElemRel) (ks : List GoString) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwOwn w sc S st c C sp ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗ isListRep tp e rel ks ∗
      ⌜S.find st.t.name = some (.list e rel ks) ∧ (l.isSome ∨ r.isSome) ∧ confO S st.t l ∧ confO S st.t r ∧ st.inLeaf = false ∧
        (C.union (cmpO S st.t st.path l r)).removed.CardLt (2 ^ 63 - 1) ∧ (C.union (cmpO S st.t st.path l r)).modified.CardLt (2 ^ 63 - 1) ∧ (C.union (cmpO S st.t st.path l r)).added.CardLt (2 ^ 63 - 1)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"doList")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      (∃ sp' : Loc, cwOwn w sc S { st with inLeaf := leafAt S st.t l r } c (C.union (cmpBelow S st.t st.path l r)) sp' ∗ ⌜sp ≠ null → sp' = sp⌝) }}

end spec

end smd
end EtcdGrove
end Perennial
