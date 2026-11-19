/-
**The recursion cluster `typed.compareWalkerRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `typed.compareWalker.compare`, `typed.compareWalker.compareListItem`, `typed.compareWalker.doList`, `typed.compareWalker.doMap`, `typed.compareWalker.visitListItems`, `typed.compareWalker.visitMapItem`, `typed.compareWalker.visitMapItems` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ typed.compareWalkerRec.specI`) and its other
callees' specs; `typed.compareWalkerRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `typed.compareWalkerRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__compare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__compareListItem
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitListItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitMapItem
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitMapItems

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

/-- `typed.compareWalker.compare.spec` inside the logic (Löb's hypothesis of `typed.compareWalkerRec`). -/
def typed.compareWalker.compare.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (dql dqr : DFrac) (l r : Option UVal) (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwOwn w sc S st c C ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      ⌜(l.isSome ∨ r.isSome) ∧ confO S st.t l ∧ confO S st.t r ∧ st.inLeaf = false ∧ (C.union (cmpO S st.t st.path l r)).removed.CardLt (2 ^ 63 - 1) ∧ (C.union (cmpO S st.t st.path l r)).modified.CardLt (2 ^ 63 - 1) ∧ (C.union (cmpO S st.t st.path l r)).added.CardLt (2 ^ 63 - 1)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"compare")) (Val #f))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      cwOwn w sc S { st with inLeaf := leafAt S st.t l r } c (C.union (cmpO S st.t st.path l r)) }})

/-- `typed.compareWalker.compareListItem.spec` inside the logic (Löb's hypothesis of `typed.compareWalkerRec`). -/
def typed.compareWalker.compareListItem.specI : IProp GF :=
  iprop(
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
      cwOwn w sc S st c (C.union (cmpO S e (st.path ++ [pe']) l r)) }})

/-- `typed.compareWalker.doList.spec` inside the logic (Löb's hypothesis of `typed.compareWalkerRec`). -/
def typed.compareWalker.doList.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (dql dqr : DFrac) (l r : Option UVal) (tp : Loc) (e : TypeRef) (rel : ElemRel) (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwOwn w sc S st c C ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗ isListRep tp e rel ks ∗
      ⌜S.find st.t.name = some (.list e rel ks) ∧ (l.isSome ∨ r.isSome) ∧ confO S st.t l ∧ confO S st.t r ∧ st.inLeaf = false ∧
        (C.union (cmpO S st.t st.path l r)).removed.CardLt (2 ^ 63 - 1) ∧ (C.union (cmpO S st.t st.path l r)).modified.CardLt (2 ^ 63 - 1) ∧ (C.union (cmpO S st.t st.path l r)).added.CardLt (2 ^ 63 - 1)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"doList")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      cwOwn w sc S { st with inLeaf := leafAt S st.t l r } c (C.union (cmpBelow S st.t st.path l r)) }})

/-- `typed.compareWalker.doMap.spec` inside the logic (Löb's hypothesis of `typed.compareWalkerRec`). -/
def typed.compareWalker.doMap.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (dql dqr : DFrac) (l r : Option UVal) (tp : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwOwn w sc S st c C ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗ isMapRep tp fs e rel ∗
      ⌜S.find st.t.name = some (.map fs e rel) ∧ (l.isSome ∨ r.isSome) ∧ confO S st.t l ∧ confO S st.t r ∧ st.inLeaf = false ∧
        (C.union (cmpO S st.t st.path l r)).removed.CardLt (2 ^ 63 - 1) ∧ (C.union (cmpO S st.t st.path l r)).modified.CardLt (2 ^ 63 - 1) ∧ (C.union (cmpO S st.t st.path l r)).added.CardLt (2 ^ 63 - 1)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"doMap")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      cwOwn w sc S { st with inLeaf := leafAt S st.t l r } c (C.union (cmpBelow S st.t st.path l r)) }})

/-- `typed.compareWalker.visitListItems.spec` inside the logic (Löb's hypothesis of `typed.compareWalkerRec`). -/
def typed.compareWalker.visitListItems.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (tp : Loc) (e : TypeRef)
    (ks : List GoString) (ll rl : value.List') (ol or_ : Option (List UVal)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwOwn w sc S st c C ∗ isListRep tp e .associative ks ∗ isListO ll ol ∗ isListO rl or_ ∗
      ⌜S.find st.t.name = some (.list e .associative ks) ∧ st.inLeaf = false ∧
        confO S st.t (ol.map UVal.list) ∧ confO S st.t (or_.map UVal.list) ∧
        (C.union (cmpListOut (fuelL (ol.getD []) (or_.getD [])) S e ks st.path (ol.getD []) (or_.getD []))).removed.CardLt (2 ^ 63 - 1) ∧
        (C.union (cmpListOut (fuelL (ol.getD []) (or_.getD [])) S e ks st.path (ol.getD []) (or_.getD []))).modified.CardLt (2 ^ 63 - 1) ∧
        (C.union (cmpListOut (fuelL (ol.getD []) (or_.getD [])) S e ks st.path (ol.getD []) (or_.getD []))).added.CardLt (2 ^ 63 - 1)⌝ }}
    (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"visitListItems")) (Val #tp)) (Val #ll)) (Val #rl))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗
      cwOwn w sc S st c (C.union (cmpListOut (fuelL (ol.getD []) (or_.getD [])) S e ks st.path
        (ol.getD []) (or_.getD []))) }})

/-- `typed.compareWalker.visitMapItem.spec` inside the logic (Löb's hypothesis of `typed.compareWalkerRec`). -/
def typed.compareWalker.visitMapItem.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (tp : Loc)
    (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel) (om : GoMap)
    (key : GoString) (t' : TypeRef) (lc rc : value.Value) (dql dqr : DFrac) (l r : Option UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwOwn w sc S st c C ∗ isMapRep tp fs e rel ∗ isValO lc dql l ∗ isValO rc dqr r ∗
      ⌜fieldType fs e key = some t' ∧ (l.isSome ∨ r.isSome) ∧ confO S t' l ∧ confO S t' r ∧
        st.inLeaf = false ∧
        (C.union (cmpO S t' (st.path ++ [.field key]) l r)).removed.CardLt (2 ^ 63 - 1) ∧
        (C.union (cmpO S t' (st.path ++ [.field key]) l r)).modified.CardLt (2 ^ 63 - 1) ∧
        (C.union (cmpO S t' (st.path ++ [.field key]) l r)).added.CardLt (2 ^ 63 - 1)⌝ }}
    (App (App (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"visitMapItem")) (Val #tp)) (Val #om)) (Val #key)) (Val #lc)) (Val #rc))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValO lc dql l ∗ isValO rc dqr r ∗
      cwOwn w sc S st c (C.union (cmpO S t' (st.path ++ [.field key]) l r)) }})

/-- `typed.compareWalker.visitMapItems.spec` inside the logic (Löb's hypothesis of `typed.compareWalkerRec`). -/
def typed.compareWalker.visitMapItems.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (tp : Loc)
    (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel) (lm rm : value.Map)
    (ol or_ : Option (List (GoString × UVal))),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwOwn w sc S st c C ∗ isMapRep tp fs e rel ∗ isMapO lm ol ∗ isMapO rm or_ ∗
      ⌜S.find st.t.name = some (.map fs e rel) ∧ st.inLeaf = false ∧
        confO S st.t (ol.map UVal.map) ∧ confO S st.t (or_.map UVal.map) ∧
        (C.union (cmpMapOut (fuelM (kvsOrEmpty ol) (kvsOrEmpty or_)) S fs e st.path (kvsOrEmpty ol) (kvsOrEmpty or_))).removed.CardLt (2 ^ 63 - 1) ∧
        (C.union (cmpMapOut (fuelM (kvsOrEmpty ol) (kvsOrEmpty or_)) S fs e st.path (kvsOrEmpty ol) (kvsOrEmpty or_))).modified.CardLt (2 ^ 63 - 1) ∧
        (C.union (cmpMapOut (fuelM (kvsOrEmpty ol) (kvsOrEmpty or_)) S fs e st.path (kvsOrEmpty ol) (kvsOrEmpty or_))).added.CardLt (2 ^ 63 - 1)⌝ }}
    (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"visitMapItems")) (Val #tp)) (Val #lm)) (Val #rm))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗
      cwOwn w sc S st c (C.union (cmpMapOut (fuelM (kvsOrEmpty ol) (kvsOrEmpty or_)) S fs e st.path
        (kvsOrEmpty ol) (kvsOrEmpty or_))) }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def typed.compareWalkerRec.specI : IProp GF :=
  iprop(typed.compareWalker.compare.specI ∧
    typed.compareWalker.compareListItem.specI ∧
    typed.compareWalker.doList.specI ∧
    typed.compareWalker.doMap.specI ∧
    typed.compareWalker.visitListItems.specI ∧
    typed.compareWalker.visitMapItem.specI ∧
    typed.compareWalker.visitMapItems.specI)

/-- **Every member's spec** (what `typed.compareWalkerRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev typed.compareWalkerRec.spec : Prop :=
  typed.compareWalker.compare.spec (GF := GF) ∧
  typed.compareWalker.compareListItem.spec (GF := GF) ∧
  typed.compareWalker.doList.spec (GF := GF) ∧
  typed.compareWalker.doMap.spec (GF := GF) ∧
  typed.compareWalker.visitListItems.spec (GF := GF) ∧
  typed.compareWalker.visitMapItem.spec (GF := GF) ∧
  typed.compareWalker.visitMapItems.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
