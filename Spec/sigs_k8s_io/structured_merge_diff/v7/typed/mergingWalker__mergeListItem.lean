/-
`mergingWalker.mergeListItem(t, pe, lChild, rChild)` (internal): merges the item of key `pe` (two
sides, one at least present, conforming to the element type) in a child walker: its output
(`outRep`: nil or a cell holding the merged item, `mergeO` at the element type). The parent
walker is given back unchanged.

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
abbrev typed.mergingWalker.mergeListItem.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : MWSt) (tp : Loc) (e : TypeRef) (rel : ElemRel)
    (ks : List GoString) (pe : fieldpath.PathElement) (pe' : PE) (lc rc : value.Value)
    (dql dqr : DFrac) (l r : Option UVal) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwOwn w sc S st sp ∗ isListRep tp e rel ks ∗ isPE pe pe' ∗ isValO lc dql l ∗ isValO rc dqr r ∗
      ⌜(l.isSome ∨ r.isSome) ∧ confO S e l ∧ confO S e r ∧ st.inLeaf = false⌝ }}
    (App (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"mergeListItem")) (Val #tp)) (Val #pe)) (Val #lc)) (Val #rc))
  {{ (o : Loc) (errs : GoSlice), RET (PairV #o #errs); (∃ sp' : Loc, mwOwn w sc S st sp' ∗ ⌜sp ≠ null → sp' = sp⌝) ∗ outRep o (mergeO S e l r) ∗
      noErrs errs ∗ isValO lc dql l ∗ isValO rc dqr r }}

end spec

end smd
end EtcdGrove
end Perennial
