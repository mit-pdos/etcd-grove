/-
`compareWalker.visitMapItem(t, out, key, lhs, rhs)` (internal; one step of `visitMapItems`'s zip):
compares the entry `key` (its type `t'`: the declared field's, else the element type) in a child
walker, adding `cmpO` at the entry's path. `out` is not used.

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
abbrev typed.compareWalker.visitMapItem.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (tp : Loc)
    (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel) (om : GoMap)
    (key : GoString) (t' : TypeRef) (lc rc : value.Value) (dql dqr : DFrac) (l r : Option UVal) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwOwn w sc S st c C sp ∗ isMapRep tp fs e rel ∗ isValO lc dql l ∗ isValO rc dqr r ∗
      ⌜(fs.map (·.1)).Nodup ∧ fieldType fs e key = some t' ∧ (l.isSome ∨ r.isSome) ∧ confO S t' l ∧ confO S t' r ∧
        st.inLeaf = false ∧
        (C.union (cmpO S t' (st.path ++ [.field key]) l r)).removed.CardLt (2 ^ 63 - 1) ∧
        (C.union (cmpO S t' (st.path ++ [.field key]) l r)).modified.CardLt (2 ^ 63 - 1) ∧
        (C.union (cmpO S t' (st.path ++ [.field key]) l r)).added.CardLt (2 ^ 63 - 1)⌝ }}
    (App (App (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"visitMapItem")) (Val #tp)) (Val #om)) (Val #key)) (Val #lc)) (Val #rc))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValO lc dql l ∗ isValO rc dqr r ∗
      (∃ sp' : Loc, cwOwn w sc S st c (C.union (cmpO S t' (st.path ++ [.field key]) l r)) sp' ∗ ⌜sp ≠ null → sp' = sp⌝) }}

end spec

end smd
end EtcdGrove
end Perennial
