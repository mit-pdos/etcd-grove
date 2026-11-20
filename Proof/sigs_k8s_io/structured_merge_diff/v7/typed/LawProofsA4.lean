/-
**Helpers of the removing walker's `doList`/`doMap` bodies** (part A4): `removeAt` of a list or
map type unfolded case by case, `removeL`/`removeM` item by item.

Prove phase, round 2 (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA3

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace LawA4

/-! ## Lists -/

/-- A list type's `removeAt` of a value not a list: `null`. -/
theorem removeAt_list_nonlist (S : Schema) (t e : TypeRef) (rel : ElemRel) (ks : List GoString)
    (R : PathSet) (x : UVal) (h : S.find t.name = some (.list e rel ks)) (hx : x.isListB = false) :
    removeAt S t R x = .null := by
  cases x <;> simp_all [removeAt, UVal.isListB]

/-- A list type's `removeAt` of an empty list or an atomic one: `null`. -/
theorem removeAt_list_leaf (S : Schema) (t e : TypeRef) (rel : ElemRel) (ks : List GoString)
    (R : PathSet) (vs : List UVal) (h : S.find t.name = some (.list e rel ks))
    (hl : vs = [] ∨ rel = .atomic) :
    removeAt S t R (.list vs) = .null := by
  rw [removeAt, h]
  rcases hl with rfl | rfl <;> simp

/-- A list type's `removeAt` of a granular non-empty list: its items' `removeL` (`null` if none
are left). -/
theorem removeAt_list_items (S : Schema) (t e : TypeRef) (rel : ElemRel) (ks : List GoString)
    (R : PathSet) (vs : List UVal) (h : S.find t.name = some (.list e rel ks))
    (hne : vs ≠ []) (hr : rel ≠ .atomic) :
    removeAt S t R (.list vs) =
      if removeL S e ks R vs = [] then .null else .list (removeL S e ks R vs) := by
  rw [removeAt, h]
  have : ¬ (vs.isEmpty = true ∨ rel = .atomic) := by
    rintro (h1 | h1)
    · exact hne (List.isEmpty_iff.1 h1)
    · exact hr h1
  simp only [this, ite_false]
  cases removeL S e ks R vs <;> simp

/-- One item of `removeL`. -/
def removeStep (S : Schema) (e : TypeRef) (ks : List GoString) (R : PathSet) (v : UVal) : List UVal :=
  match keyOf ks v with
  | some pe =>
    if [pe] ∈ R then []
    else if ¬ (R.under pe).IsEmpty then [removeAt S e (R.under pe) v]
    else [v]
  | none => [v]

theorem removeL_cons (S : Schema) (e : TypeRef) (ks : List GoString) (R : PathSet) (v : UVal)
    (vs : List UVal) : removeL S e ks R (v :: vs) = removeStep S e ks R v ++ removeL S e ks R vs := by
  rw [removeL]
  unfold removeStep
  cases keyOf ks v with
  | none => rfl
  | some pe =>
    simp only
    by_cases h1 : [pe] ∈ R
    · simp [h1]
    · by_cases h2 : (R.under pe).IsEmpty <;> simp [h1, h2]

theorem removeL_append (S : Schema) (e : TypeRef) (ks : List GoString) (R : PathSet) :
    ∀ (a b : List UVal), removeL S e ks R (a ++ b) = removeL S e ks R a ++ removeL S e ks R b
  | [], b => by simp [removeL]
  | v :: a, b => by
    rw [List.cons_append, removeL_cons, removeL_cons, removeL_append S e ks R a b,
      List.append_assoc]

theorem removeL_take_succ (S : Schema) (e : TypeRef) (ks : List GoString) (R : PathSet)
    (vs : List UVal) (j : Nat) (x : UVal) (hx : vs[j]? = some x) :
    removeL S e ks R (vs.take (j + 1)) = removeL S e ks R (vs.take j) ++ removeStep S e ks R x := by
  rw [List.take_add_one, hx]
  simp only [Option.toList_some, removeL_append, removeL_cons]
  simp [removeL]

end LawA4

end smd
end EtcdGrove
end Perennial
