/-
**The recursion cluster `typed.reconcileWithSchemaWalkerRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `typed.reconcileWithSchemaWalker.doList`, `typed.reconcileWithSchemaWalker.doMap`, `typed.reconcileWithSchemaWalker.reconcile`, `typed.reconcileWithSchemaWalker.visitListItems`, `typed.reconcileWithSchemaWalker.visitMapItems` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ typed.reconcileWithSchemaWalkerRec.specI`) and its other
callees' specs; `typed.reconcileWithSchemaWalkerRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `typed.reconcileWithSchemaWalkerRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__doList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__doMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__reconcile
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__visitListItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__visitMapItems

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

/-- `typed.reconcileWithSchemaWalker.doList.spec` inside the logic (Löb's hypothesis of `typed.reconcileWithSchemaWalkerRec`). -/
def typed.reconcileWithSchemaWalker.doList.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : RWSt) (F R A : Option PathSet) (tp : Loc) (e : TypeRef) (rel : ElemRel) (ks : List GoString) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rwOwn w sc S st F R A sp ∗ isListRep tp e rel ks ∗ ⌜S.find st.t.name = some (.list e rel ks) ∧ (st.isAtomic = true → F = none) ∧ (F.getD PathSet.empty).CardLt (2 ^ 63)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker.ty @!! go!"doList")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ ∃ R' A' : Option PathSet, (∃ sp' : Loc, rwOwn w sc S st F R' A' sp' ∗ ⌜sp ≠ null → sp' = sp⌝) ∗
      ⌜optU R R' = optU R (reconOut S st.t st.path st.isAtomic (F.getD PathSet.empty)) ∧
        optU A A' = optU A (reconOut S st.t st.path st.isAtomic (F.getD PathSet.empty))⌝ }})

/-- `typed.reconcileWithSchemaWalker.doMap.spec` inside the logic (Löb's hypothesis of `typed.reconcileWithSchemaWalkerRec`). -/
def typed.reconcileWithSchemaWalker.doMap.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : RWSt) (F R A : Option PathSet) (tp : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rwOwn w sc S st F R A sp ∗ isMapRep tp fs e rel ∗ ⌜S.find st.t.name = some (.map fs e rel) ∧ (st.isAtomic = true → F = none) ∧ (F.getD PathSet.empty).CardLt (2 ^ 63)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker.ty @!! go!"doMap")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ ∃ R' A' : Option PathSet, (∃ sp' : Loc, rwOwn w sc S st F R' A' sp' ∗ ⌜sp ≠ null → sp' = sp⌝) ∗
      ⌜optU R R' = optU R (reconOut S st.t st.path st.isAtomic (F.getD PathSet.empty)) ∧
        optU A A' = optU A (reconOut S st.t st.path st.isAtomic (F.getD PathSet.empty))⌝ }})

/-- `typed.reconcileWithSchemaWalker.reconcile.spec` inside the logic (Löb's hypothesis of `typed.reconcileWithSchemaWalkerRec`). -/
def typed.reconcileWithSchemaWalker.reconcile.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : RWSt) (F R A : Option PathSet) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rwOwn w sc S st F R A sp ∗ ⌜(S.find st.t.name).isSome ∧ (st.isAtomic = true → F = none) ∧ (F.getD PathSet.empty).CardLt (2 ^ 63)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker.ty @!! go!"reconcile")) (Val #()))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ ∃ R' A' : Option PathSet, (∃ sp' : Loc, rwOwn w sc S st F R' A' sp' ∗ ⌜sp ≠ null → sp' = sp⌝) ∗
      ⌜optU R R' = optU R (reconOut S st.t st.path st.isAtomic (F.getD PathSet.empty)) ∧
        optU A A' = optU A (reconOut S st.t st.path st.isAtomic (F.getD PathSet.empty))⌝ }})

/-- `typed.reconcileWithSchemaWalker.visitListItems.spec` inside the logic (Löb's hypothesis of `typed.reconcileWithSchemaWalkerRec`). -/
def typed.reconcileWithSchemaWalker.visitListItems.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : RWSt) (R A : Option PathSet) (tp : Loc) (e : TypeRef) (rel : ElemRel) (ks : List GoString) (ep : Loc)
    (F : PathSet) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rwOwn w sc S st (some F) R A sp ∗ isListRep tp e rel ks ∗ isSet ep F ∗
      ⌜S.find st.t.name = some (.list e rel ks) ∧ rel ≠ .atomic ∧ F.CardLt (2 ^ 63)⌝ }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker.ty @!! go!"visitListItems")) (Val #tp)) (Val #ep))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ ∃ R' A' : Option PathSet, (∃ sp' : Loc, rwOwn w sc S st (some F) R' A' sp' ∗ ⌜sp ≠ null → sp' = sp⌝) ∗
      ⌜optU R R' = optU R (reconBelow S st.t st.path F) ∧ optU A A' = optU A (reconBelow S st.t st.path F)⌝ }})

/-- `typed.reconcileWithSchemaWalker.visitMapItems.spec` inside the logic (Löb's hypothesis of `typed.reconcileWithSchemaWalkerRec`). -/
def typed.reconcileWithSchemaWalker.visitMapItems.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : RWSt) (R A : Option PathSet) (tp : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel) (ep : Loc)
    (F : PathSet) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rwOwn w sc S st (some F) R A sp ∗ isMapRep tp fs e rel ∗ isSet ep F ∗
      ⌜S.find st.t.name = some (.map fs e rel) ∧ rel ≠ .atomic ∧ F.CardLt (2 ^ 63)⌝ }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker.ty @!! go!"visitMapItems")) (Val #tp)) (Val #ep))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ ∃ R' A' : Option PathSet, (∃ sp' : Loc, rwOwn w sc S st (some F) R' A' sp' ∗ ⌜sp ≠ null → sp' = sp⌝) ∗
      ⌜optU R R' = optU R (reconBelow S st.t st.path F) ∧ optU A A' = optU A (reconBelow S st.t st.path F)⌝ }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def typed.reconcileWithSchemaWalkerRec.specI : IProp GF :=
  iprop(typed.reconcileWithSchemaWalker.doList.specI ∧
    typed.reconcileWithSchemaWalker.doMap.specI ∧
    typed.reconcileWithSchemaWalker.reconcile.specI ∧
    typed.reconcileWithSchemaWalker.visitListItems.specI ∧
    typed.reconcileWithSchemaWalker.visitMapItems.specI)

/-- **Every member's spec** (what `typed.reconcileWithSchemaWalkerRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev typed.reconcileWithSchemaWalkerRec.spec : Prop :=
  typed.reconcileWithSchemaWalker.doList.spec (GF := GF) ∧
  typed.reconcileWithSchemaWalker.doMap.spec (GF := GF) ∧
  typed.reconcileWithSchemaWalker.reconcile.spec (GF := GF) ∧
  typed.reconcileWithSchemaWalker.visitListItems.spec (GF := GF) ∧
  typed.reconcileWithSchemaWalker.visitMapItems.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
