/-
**The recursion cluster `typed.mergingWalkerRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `typed.mergingWalker.doList`, `typed.mergingWalker.doMap`, `typed.mergingWalker.merge`, `typed.mergingWalker.mergeListItem`, `typed.mergingWalker.visitListItems`, `typed.mergingWalker.visitMapItem`, `typed.mergingWalker.visitMapItems` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ typed.mergingWalkerRec.specI`) and its other
callees' specs; `typed.mergingWalkerRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `typed.mergingWalkerRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__merge
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__mergeListItem
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__visitListItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__visitMapItem
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__visitMapItems

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

/-- `typed.mergingWalker.doList.spec` inside the logic (Löb's hypothesis of `typed.mergingWalkerRec`). -/
def typed.mergingWalker.doList.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : MWSt) (dql dqr : DFrac) (l r : Option UVal) (tp : Loc)
    (e : TypeRef) (rel : ElemRel) (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwOwn w sc S st ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗ isListRep tp e rel ks ∗
      ⌜S.find st.t.name = some (.list e rel ks) ∧ (l.isSome ∨ r.isSome) ∧ confO S st.t l ∧ confO S st.t r ∧ st.out = none ∧
        st.inLeaf = false⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"doList")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      mwOwn w sc S { st with out := mergeO S st.t l r, inLeaf := leafAt S st.t l r } }})

/-- `typed.mergingWalker.doMap.spec` inside the logic (Löb's hypothesis of `typed.mergingWalkerRec`). -/
def typed.mergingWalker.doMap.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : MWSt) (dql dqr : DFrac) (l r : Option UVal) (tp : Loc)
    (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwOwn w sc S st ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗ isMapRep tp fs e rel ∗
      ⌜S.find st.t.name = some (.map fs e rel) ∧ (l.isSome ∨ r.isSome) ∧ confO S st.t l ∧ confO S st.t r ∧ st.out = none ∧
        st.inLeaf = false⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"doMap")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      mwOwn w sc S { st with out := mergeO S st.t l r, inLeaf := leafAt S st.t l r } }})

/-- `typed.mergingWalker.merge.spec` inside the logic (Löb's hypothesis of `typed.mergingWalkerRec`). -/
def typed.mergingWalker.merge.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : MWSt) (dql dqr : DFrac) (l r : Option UVal) (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwOwn w sc S st ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      ⌜(l.isSome ∨ r.isSome) ∧ confO S st.t l ∧ confO S st.t r ∧ st.out = none ∧ st.inLeaf = false⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"merge")) (Val #f))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      mwOwn w sc S { st with out := mergeO S st.t l r, inLeaf := leafAt S st.t l r } }})

/-- `typed.mergingWalker.mergeListItem.spec` inside the logic (Löb's hypothesis of `typed.mergingWalkerRec`). -/
def typed.mergingWalker.mergeListItem.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : MWSt) (tp : Loc) (e : TypeRef) (rel : ElemRel)
    (ks : List GoString) (pe : fieldpath.PathElement) (pe' : PE) (lc rc : value.Value)
    (dql dqr : DFrac) (l r : Option UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwOwn w sc S st ∗ isListRep tp e rel ks ∗ isPE pe pe' ∗ isValO lc dql l ∗ isValO rc dqr r ∗
      ⌜(l.isSome ∨ r.isSome) ∧ confO S e l ∧ confO S e r ∧ st.inLeaf = false⌝ }}
    (App (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"mergeListItem")) (Val #tp)) (Val #pe)) (Val #lc)) (Val #rc))
  {{ (o : Loc) (errs : GoSlice), RET (PairV #o #errs); mwOwn w sc S st ∗ outRep o (mergeO S e l r) ∗
      noErrs errs ∗ isValO lc dql l ∗ isValO rc dqr r }})

/-- `typed.mergingWalker.visitListItems.spec` inside the logic (Löb's hypothesis of `typed.mergingWalkerRec`). -/
def typed.mergingWalker.visitListItems.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : MWSt) (tp : Loc) (e : TypeRef) (ks : List GoString)
    (ll rl : value.List') (ol or_ : Option (List UVal)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwOwn w sc S st ∗ isListRep tp e .associative ks ∗ isListO ll ol ∗ isListO rl or_ ∗
      ⌜S.find st.t.name = some (.list e .associative ks) ∧ st.out = none ∧ st.inLeaf = false ∧
        confO S st.t (ol.map UVal.list) ∧ confO S st.t (or_.map UVal.list)⌝ }}
    (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"visitListItems")) (Val #tp)) (Val #ll)) (Val #rl))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗
      mwOwn w sc S { st with out := (mergeListOut (fuelL (ol.getD []) (or_.getD [])) S e ks
        (ol.getD []) (or_.getD [])) } }})

/-- `typed.mergingWalker.visitMapItem.spec` inside the logic (Löb's hypothesis of `typed.mergingWalkerRec`). -/
def typed.mergingWalker.visitMapItem.specI : IProp GF :=
  iprop(
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
      | some x => iprop(∃ i : GoInterface, om ↦$ (<[key := i]> M) ∗ isIface i x) }})

/-- `typed.mergingWalker.visitMapItems.spec` inside the logic (Löb's hypothesis of `typed.mergingWalkerRec`). -/
def typed.mergingWalker.visitMapItems.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : MWSt) (tp : Loc) (fs : List (GoString × TypeRef))
    (e : Option TypeRef) (rel : ElemRel) (lm rm : value.Map)
    (ol or_ : Option (List (GoString × UVal))),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwOwn w sc S st ∗ isMapRep tp fs e rel ∗ isMapO lm ol ∗ isMapO rm or_ ∗
      ⌜S.find st.t.name = some (.map fs e rel) ∧ st.out = none ∧ st.inLeaf = false ∧
        confO S st.t (ol.map UVal.map) ∧ confO S st.t (or_.map UVal.map)⌝ }}
    (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"visitMapItems")) (Val #tp)) (Val #lm)) (Val #rm))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗
      mwOwn w sc S { st with out := (mergeMapOut (fuelM (kvsOrEmpty ol) (kvsOrEmpty or_)) S fs e
        (kvsOrEmpty ol) (kvsOrEmpty or_)) } }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def typed.mergingWalkerRec.specI : IProp GF :=
  iprop(typed.mergingWalker.doList.specI ∧
    typed.mergingWalker.doMap.specI ∧
    typed.mergingWalker.merge.specI ∧
    typed.mergingWalker.mergeListItem.specI ∧
    typed.mergingWalker.visitListItems.specI ∧
    typed.mergingWalker.visitMapItem.specI ∧
    typed.mergingWalker.visitMapItems.specI)

/-- **Every member's spec** (what `typed.mergingWalkerRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev typed.mergingWalkerRec.spec : Prop :=
  typed.mergingWalker.doList.spec (GF := GF) ∧
  typed.mergingWalker.doMap.spec (GF := GF) ∧
  typed.mergingWalker.merge.spec (GF := GF) ∧
  typed.mergingWalker.mergeListItem.spec (GF := GF) ∧
  typed.mergingWalker.visitListItems.spec (GF := GF) ∧
  typed.mergingWalker.visitMapItem.spec (GF := GF) ∧
  typed.mergingWalker.visitMapItems.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
