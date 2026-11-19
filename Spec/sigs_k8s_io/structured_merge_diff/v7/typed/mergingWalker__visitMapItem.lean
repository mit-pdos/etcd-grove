/-
`mergingWalker.visitMapItem(t, out, key, lhs, rhs)` (internal; one step of `visitMapItems`'s zip):
merges the entry `key` (two sides, one at least present, conforming to the key's type `t'`: the
declared field's, else the element type) in a child walker, and stores the merged value in the
map `out` under `key` unless the merge is absent. The parent walker is given back unchanged.

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
abbrev typed.mergingWalker.visitMapItem.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : MWSt) (tp : Loc) (fs : List (GoString × TypeRef))
    (e : Option TypeRef) (rel : ElemRel) (om : GoMap) (M : GMap GoString GoInterface)
    (key : GoString) (t' : TypeRef) (lc rc : value.Value) (dql dqr : DFrac) (l r : Option UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwOwn w sc S st ∗ isMapRep tp fs e rel ∗ om ↦$ M ∗ isValO lc dql l ∗ isValO rc dqr r ∗
      ⌜fieldType fs e key = some t' ∧ (l.isSome ∨ r.isSome) ∧ confO S t' l ∧ confO S t' r ∧
        st.inLeaf = false⌝ }}
    (App (App (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"visitMapItem")) (Val #tp)) (Val #om)) (Val #key)) (Val #lc)) (Val #rc))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ mwOwn w sc S st ∗ isValO lc dql l ∗ isValO rc dqr r ∗
      match mergeO S t' l r with
      | none => iprop(om ↦$ M)
      | some x => iprop(∃ i : GoInterface, om ↦$ (<[key := i]> M) ∗ isIface i x) }}

end spec

end smd
end EtcdGrove
end Perennial
