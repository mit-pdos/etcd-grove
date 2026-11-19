/-
**The recursion cluster `typed.toFieldSetWalkerRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `typed.toFieldSetWalker.doList`, `typed.toFieldSetWalker.doMap`, `typed.toFieldSetWalker.toFieldSet`, `typed.toFieldSetWalker.visitListItems`, `typed.toFieldSetWalker.visitMapItems` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ typed.toFieldSetWalkerRec.specI`) and its other
callees' specs; `typed.toFieldSetWalkerRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `typed.toFieldSetWalkerRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__doList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__doMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__toFieldSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__visitListItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__visitMapItems

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

/-- `typed.toFieldSetWalker.doList.spec` inside the logic (Löb's hypothesis of `typed.toFieldSetWalkerRec`). -/
def typed.toFieldSetWalker.doList.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : TWSt) (s : Loc) (F : PathSet) (dq : DFrac) (x : UVal) (tp : Loc) (e : TypeRef) (rel : ElemRel) (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ twOwn w sc S st s F ∗ isValF st.value dq x ∗ isListRep tp e rel ks ∗ ⌜S.find st.t.name = some (.list e rel ks) ∧ conforms S st.t x ∧ (F.union (fieldsAt S st.t st.path x)).CardLt (2 ^ 63 - 1)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker.ty @!! go!"doList")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValF st.value dq x ∗
      twOwn w sc S st s (F.union (fieldsAt S st.t st.path x)) }})

/-- `typed.toFieldSetWalker.doMap.spec` inside the logic (Löb's hypothesis of `typed.toFieldSetWalkerRec`). -/
def typed.toFieldSetWalker.doMap.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : TWSt) (s : Loc) (F : PathSet) (dq : DFrac) (x : UVal) (tp : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ twOwn w sc S st s F ∗ isValF st.value dq x ∗ isMapRep tp fs e rel ∗ ⌜S.find st.t.name = some (.map fs e rel) ∧ conforms S st.t x ∧ (F.union (fieldsAt S st.t st.path x)).CardLt (2 ^ 63 - 1)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker.ty @!! go!"doMap")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValF st.value dq x ∗
      twOwn w sc S st s (F.union (fieldsAt S st.t st.path x)) }})

/-- `typed.toFieldSetWalker.toFieldSet.spec` inside the logic (Löb's hypothesis of `typed.toFieldSetWalkerRec`). -/
def typed.toFieldSetWalker.toFieldSet.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : TWSt) (s : Loc) (F : PathSet) (dq : DFrac) (x : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ twOwn w sc S st s F ∗ isValF st.value dq x ∗ ⌜conforms S st.t x ∧ (F.union (fieldsAt S st.t st.path x)).CardLt (2 ^ 63 - 1)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker.ty @!! go!"toFieldSet")) (Val #()))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValF st.value dq x ∗
      twOwn w sc S st s (F.union (fieldsAt S st.t st.path x)) }})

/-- `typed.toFieldSetWalker.visitListItems.spec` inside the logic (Löb's hypothesis of `typed.toFieldSetWalkerRec`). -/
def typed.toFieldSetWalker.visitListItems.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : TWSt) (s : Loc) (F : PathSet) (tp : Loc) (e : TypeRef)
    (ks : List GoString) (ll : value.List') (vs : List UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ twOwn w sc S st s F ∗ isListRep tp e .associative ks ∗ isListV ll vs ∗
      ⌜S.find st.t.name = some (.list e .associative ks) ∧ conforms S st.t (.list vs) ∧
        (F.union (fieldsL S e ks st.path vs)).CardLt (2 ^ 63 - 1)⌝ }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker.ty @!! go!"visitListItems")) (Val #tp)) (Val #ll))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ twOwn w sc S st s (F.union (fieldsL S e ks st.path vs)) }})

/-- `typed.toFieldSetWalker.visitMapItems.spec` inside the logic (Löb's hypothesis of `typed.toFieldSetWalkerRec`). -/
def typed.toFieldSetWalker.visitMapItems.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (st : TWSt) (s : Loc) (F : PathSet) (tp : Loc)
    (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel) (m : value.Map)
    (kvs : List (GoString × UVal)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ twOwn w sc S st s F ∗ isMapRep tp fs e rel ∗ isMapV m kvs ∗
      ⌜S.find st.t.name = some (.map fs e rel) ∧ conforms S st.t (.map kvs) ∧
        (F.union (fieldsM S fs e st.path kvs)).CardLt (2 ^ 63 - 1)⌝ }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker.ty @!! go!"visitMapItems")) (Val #tp)) (Val #m))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ twOwn w sc S st s (F.union (fieldsM S fs e st.path kvs)) }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def typed.toFieldSetWalkerRec.specI : IProp GF :=
  iprop(typed.toFieldSetWalker.doList.specI ∧
    typed.toFieldSetWalker.doMap.specI ∧
    typed.toFieldSetWalker.toFieldSet.specI ∧
    typed.toFieldSetWalker.visitListItems.specI ∧
    typed.toFieldSetWalker.visitMapItems.specI)

/-- **Every member's spec** (what `typed.toFieldSetWalkerRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev typed.toFieldSetWalkerRec.spec : Prop :=
  typed.toFieldSetWalker.doList.spec (GF := GF) ∧
  typed.toFieldSetWalker.doMap.spec (GF := GF) ∧
  typed.toFieldSetWalker.toFieldSet.spec (GF := GF) ∧
  typed.toFieldSetWalker.visitListItems.spec (GF := GF) ∧
  typed.toFieldSetWalker.visitMapItems.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
