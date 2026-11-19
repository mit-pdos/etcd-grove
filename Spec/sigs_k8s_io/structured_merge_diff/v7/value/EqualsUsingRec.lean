/-
**The recursion cluster `value.EqualsUsingRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `value.EqualsUsing`, `value.ListEqualsUsing`, `value.listUnstructured.EqualsUsing`, `value.listUnstructured.EqualsUsing_ptr`, `value.mapUnstructuredString.EqualsUsing` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ value.EqualsUsingRec.specI`) and its other
callees' specs; `value.EqualsUsingRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `value.EqualsUsingRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.EqualsUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.ListEqualsUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__EqualsUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__EqualsUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__EqualsUsing

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
variable [package_sem : value.Assumptions]

/-- `value.EqualsUsing.spec` inside the logic (Löb's hypothesis of `value.EqualsUsingRec`). -/
def value.EqualsUsing.specI : IProp GF :=
  iprop(
  ∀ (al : value.Allocator) (a b : value.Value) (dq1 dq2 : DFrac) (x y : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc al ∗ isValF a dq1 x ∗ isValF b dq2 y }}
    (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.EqualsUsing)) (Val #al)) (Val #a)) (Val #b))
  {{ (r : Bool), RET #r; isAlloc al ∗ isValF a dq1 x ∗ isValF b dq2 y ∗ ⌜r = true ↔ x = y⌝ }})

/-- `value.ListEqualsUsing.spec` inside the logic (Löb's hypothesis of `value.EqualsUsingRec`). -/
def value.ListEqualsUsing.specI : IProp GF :=
  iprop(
  ∀ (al : value.Allocator) (l r : value.List') (xs ys : List UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc al ∗ isListV l xs ∗ isListV r ys }}
    (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.ListEqualsUsing)) (Val #al)) (Val #l)) (Val #r))
  {{ (b : Bool), RET #b; isAlloc al ∗ ⌜b = true ↔ xs = ys⌝ }})

/-- `value.listUnstructured.EqualsUsing.spec` inside the logic (Löb's hypothesis of `value.EqualsUsingRec`). -/
def value.listUnstructured.EqualsUsing.specI : IProp GF :=
  iprop(
  ∀ (l : GoSlice) (vs ws : List UVal) (al : value.Allocator) (o : value.List'),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isListV (interface.mkOk value.listUnstructured.ty #l) vs ∗ isListV o ws ∗ isAlloc al }}
    (App (App (Val (l @!! value.listUnstructured.ty @!! go!"EqualsUsing")) (Val #al)) (Val #o))
  {{ (b : Bool), RET #b; isAlloc al ∗ ⌜b = true ↔ vs = ws⌝ }})

/-- `value.listUnstructured.EqualsUsing_ptr.spec` inside the logic (Löb's hypothesis of `value.EqualsUsingRec`). -/
def value.listUnstructured.EqualsUsing_ptr.specI : IProp GF :=
  iprop(
  ∀ (p : Loc) (vs ws : List UVal) (al : value.Allocator) (o : value.List'),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isListV (interface.mkOk (go.GoType.PointerType value.listUnstructured.ty) #p) vs ∗ isListV o ws ∗ isAlloc al }}
    (App (App (Val (p @!! (go.GoType.PointerType value.listUnstructured.ty) @!! go!"EqualsUsing")) (Val #al)) (Val #o))
  {{ (b : Bool), RET #b; isAlloc al ∗ ⌜b = true ↔ vs = ws⌝ }})

/-- `value.mapUnstructuredString.EqualsUsing.spec` inside the logic (Löb's hypothesis of `value.EqualsUsingRec`). -/
def value.mapUnstructuredString.EqualsUsing.specI : IProp GF :=
  iprop(
  ∀ (m : GoMap) (kvs kvs' : List (GoString × UVal)) (al : value.Allocator) (o : value.Map),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isMapV (interface.mkOk value.mapUnstructuredString.ty #m) kvs ∗ isMapV o kvs' ∗ isAlloc al }}
    (App (App (Val (m @!! value.mapUnstructuredString.ty @!! go!"EqualsUsing")) (Val #al)) (Val #o))
  {{ (r : Bool), RET #r; isAlloc al ∗ ⌜r = true ↔ kvs = kvs'⌝ }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def value.EqualsUsingRec.specI : IProp GF :=
  iprop(value.EqualsUsing.specI ∧
    value.ListEqualsUsing.specI ∧
    value.listUnstructured.EqualsUsing.specI ∧
    value.listUnstructured.EqualsUsing_ptr.specI ∧
    value.mapUnstructuredString.EqualsUsing.specI)

/-- **Every member's spec** (what `value.EqualsUsingRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev value.EqualsUsingRec.spec : Prop :=
  value.EqualsUsing.spec (GF := GF) ∧
  value.ListEqualsUsing.spec (GF := GF) ∧
  value.listUnstructured.EqualsUsing.spec (GF := GF) ∧
  value.listUnstructured.EqualsUsing_ptr.spec (GF := GF) ∧
  value.mapUnstructuredString.EqualsUsing.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
