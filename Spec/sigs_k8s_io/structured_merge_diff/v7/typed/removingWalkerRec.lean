/-
**The recursion cluster `typed.removingWalkerRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `typed.removeItemsWithSchema`, `typed.removingWalker.doList`, `typed.removingWalker.doMap` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ typed.removingWalkerRec.specI`) and its other
callees' specs; `typed.removingWalkerRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `typed.removingWalkerRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removeItemsWithSchema
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doMap

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

/-- `typed.removeItemsWithSchema.spec` inside the logic (Löb's hypothesis of `typed.removingWalkerRec`). -/
def typed.removeItemsWithSchema.specI : IProp GF :=
  iprop(
  ∀ (v : value.Value) (dq : DFrac) (x : UVal) (rp sc : Loc) (R : PathSet) (S : Schema)
    (tr : schema.TypeRef) (t : TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isValF v dq x ∗ isSet rp R ∗ isSchema sc S ∗ isTypeRef tr t ∗ ⌜S.WF ∧ conforms S t x⌝ }}
    (App (App (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.removeItemsWithSchema)) (Val #v)) (Val #rp)) (Val #sc)) (Val #tr)) (Val #false))
  {{ (v' : value.Value), RET #v'; isValF v dq x ∗ isValF v' (DFrac.own 1) (removeAt S t R x) }})

/-- `typed.removingWalker.doList.spec` inside the logic (Löb's hypothesis of `typed.removingWalkerRec`). -/
def typed.removingWalker.doList.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (v : value.Value) (dq : DFrac) (x : UVal) (rp : Loc) (R : PathSet) (a : value.Allocator) (t : TypeRef) (tp : Loc) (e : TypeRef) (rel : ElemRel) (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rmOwn w sc S v rp R a interface.nil ∗ isValF v dq x ∗ isListRep tp e rel ks ∗ ⌜S.find t.name = some (.list e rel ks) ∧ conforms S t x⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker.ty @!! go!"doList")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; ∃ out : GoInterface, rmOwn w sc S v rp R a out ∗ isIface out (removeAt S t R x) ∗ isValF v dq x }})

/-- `typed.removingWalker.doMap.spec` inside the logic (Löb's hypothesis of `typed.removingWalkerRec`). -/
def typed.removingWalker.doMap.specI : IProp GF :=
  iprop(
  ∀ (w sc : Loc) (S : Schema) (v : value.Value) (dq : DFrac) (x : UVal) (rp : Loc) (R : PathSet) (a : value.Allocator) (t : TypeRef) (tp : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rmOwn w sc S v rp R a interface.nil ∗ isValF v dq x ∗ isMapRep tp fs e rel ∗ ⌜S.find t.name = some (.map fs e rel) ∧ conforms S t x⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker.ty @!! go!"doMap")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; ∃ out : GoInterface, rmOwn w sc S v rp R a out ∗ isIface out (removeAt S t R x) ∗ isValF v dq x }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def typed.removingWalkerRec.specI : IProp GF :=
  iprop(typed.removeItemsWithSchema.specI ∧
    typed.removingWalker.doList.specI ∧
    typed.removingWalker.doMap.specI)

/-- **Every member's spec** (what `typed.removingWalkerRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev typed.removingWalkerRec.spec : Prop :=
  typed.removeItemsWithSchema.spec (GF := GF) ∧
  typed.removingWalker.doList.spec (GF := GF) ∧
  typed.removingWalker.doMap.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
