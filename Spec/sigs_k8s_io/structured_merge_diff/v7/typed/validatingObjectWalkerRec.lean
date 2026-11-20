/-
**The recursion cluster `typed.validatingObjectWalkerRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `typed.validatingObjectWalker.doList`, `typed.validatingObjectWalker.doMap`, `typed.validatingObjectWalker.validate`, `typed.validatingObjectWalker.visitListItems`, `typed.validatingObjectWalker.visitMapItems` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ typed.validatingObjectWalkerRec.specI`) and its other
callees' specs; `typed.validatingObjectWalkerRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `typed.validatingObjectWalkerRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__doList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__doMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__validate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__visitListItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__visitMapItems

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

/-- `typed.validatingObjectWalker.doList.spec` inside the logic (Löb's hypothesis of `typed.validatingObjectWalkerRec`). -/
def typed.validatingObjectWalker.doList.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : VWSt) (dq : DFrac) (x : UVal) (tp : Loc) (e : TypeRef) (rel : ElemRel) (ks : List GoString) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ vwOwn w sc S st sp ∗ isValF st.value dq x ∗ isListRep tp e rel ks ∗ ⌜S.find st.t.name = some (.list e rel ks)⌝ ∗ ⌜conforms S st.t x⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker.ty @!! go!"doList")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValF st.value dq x ∗
      (∃ sp' : Loc, vwOwn w sc S st sp' ∗ ⌜sp ≠ null → sp' = sp⌝) }})

/-- `typed.validatingObjectWalker.doMap.spec` inside the logic (Löb's hypothesis of `typed.validatingObjectWalkerRec`). -/
def typed.validatingObjectWalker.doMap.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : VWSt) (dq : DFrac) (x : UVal) (tp : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ vwOwn w sc S st sp ∗ isValF st.value dq x ∗ isMapRep tp fs e rel ∗ ⌜S.find st.t.name = some (.map fs e rel)⌝ ∗ ⌜conforms S st.t x⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker.ty @!! go!"doMap")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValF st.value dq x ∗
      (∃ sp' : Loc, vwOwn w sc S st sp' ∗ ⌜sp ≠ null → sp' = sp⌝) }})

/-- `typed.validatingObjectWalker.validate.spec` inside the logic (Löb's hypothesis of `typed.validatingObjectWalkerRec`). -/
def typed.validatingObjectWalker.validate.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : VWSt) (dq : DFrac) (x : UVal) (f : GoFunc) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ vwOwn w sc S st sp ∗ isValF st.value dq x ∗ ⌜(S.find st.t.name).isSome⌝ ∗ ⌜conforms S st.t x⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker.ty @!! go!"validate")) (Val #f))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValF st.value dq x ∗
      (∃ sp' : Loc, vwOwn w sc S st sp' ∗ ⌜sp ≠ null → sp' = sp⌝) }})

/-- `typed.validatingObjectWalker.visitListItems.spec` inside the logic (Löb's hypothesis of `typed.validatingObjectWalkerRec`). -/
def typed.validatingObjectWalker.visitListItems.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : VWSt) (tp : Loc) (e : TypeRef) (rel : ElemRel)
    (ks : List GoString) (ll : value.List') (vs : List UVal) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ vwOwn w sc S st sp ∗ isListRep tp e rel ks ∗ isListV ll vs ∗
      ⌜S.find st.t.name = some (.list e rel ks) ∧ conforms S st.t (.list vs)⌝ }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker.ty @!! go!"visitListItems")) (Val #tp)) (Val #ll))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ (∃ sp' : Loc, vwOwn w sc S st sp' ∗ ⌜sp ≠ null → sp' = sp⌝) }})

/-- `typed.validatingObjectWalker.visitMapItems.spec` inside the logic (Löb's hypothesis of `typed.validatingObjectWalkerRec`). -/
def typed.validatingObjectWalker.visitMapItems.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : VWSt) (tp : Loc) (fs : List (GoString × TypeRef))
    (e : Option TypeRef) (rel : ElemRel) (m : value.Map) (kvs : List (GoString × UVal)) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ vwOwn w sc S st sp ∗ isMapRep tp fs e rel ∗ isMapV m kvs ∗
      ⌜S.find st.t.name = some (.map fs e rel) ∧ conforms S st.t (.map kvs)⌝ }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker.ty @!! go!"visitMapItems")) (Val #tp)) (Val #m))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ (∃ sp' : Loc, vwOwn w sc S st sp' ∗ ⌜sp ≠ null → sp' = sp⌝) }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def typed.validatingObjectWalkerRec.specI : IProp GF :=
  iprop(typed.validatingObjectWalker.doList.specI ∧
    typed.validatingObjectWalker.doMap.specI ∧
    typed.validatingObjectWalker.validate.specI ∧
    typed.validatingObjectWalker.visitListItems.specI ∧
    typed.validatingObjectWalker.visitMapItems.specI)

/-- **Every member's spec** (what `typed.validatingObjectWalkerRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev typed.validatingObjectWalkerRec.spec : Prop :=
  typed.validatingObjectWalker.doList.spec (GF := GF) ∧
  typed.validatingObjectWalker.doMap.spec (GF := GF) ∧
  typed.validatingObjectWalker.validate.spec (GF := GF) ∧
  typed.validatingObjectWalker.visitListItems.spec (GF := GF) ∧
  typed.validatingObjectWalker.visitMapItems.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
