/-
`compareWalker.compareListItem(t, pe, lChild, rChild)` (internal): compares the item of key `pe`
(two sides, one at least present, conforming to the element type) in a child walker, adding
`cmpO` at the item's path to the comparison. The parent walker is given back unchanged.

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
abbrev typed.compareWalker.compareListItem.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (tp : Loc) (e : TypeRef)
    (rel : ElemRel) (ks : List GoString) (pe : fieldpath.PathElement) (pe' : PE)
    (lc rc : value.Value) (dql dqr : DFrac) (l r : Option UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwOwn w sc S st c C ∗ isListRep tp e rel ks ∗ isPE pe pe' ∗ isValO lc dql l ∗ isValO rc dqr r ∗
      ⌜(l.isSome ∨ r.isSome) ∧ confO S e l ∧ confO S e r ∧ st.inLeaf = false ∧
        (C.union (cmpO S e (st.path ++ [pe']) l r)).removed.CardLt (2 ^ 63 - 1) ∧
        (C.union (cmpO S e (st.path ++ [pe']) l r)).modified.CardLt (2 ^ 63 - 1) ∧
        (C.union (cmpO S e (st.path ++ [pe']) l r)).added.CardLt (2 ^ 63 - 1)⌝ }}
    (App (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"compareListItem")) (Val #tp)) (Val #pe)) (Val #lc)) (Val #rc))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValO lc dql l ∗ isValO rc dqr r ∗
      cwOwn w sc S st c (C.union (cmpO S e (st.path ++ [pe']) l r)) }}

end spec

end smd
end EtcdGrove
end Perennial
