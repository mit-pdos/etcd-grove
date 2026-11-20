/-
Pure helpers of the reconcile walker's proofs (`reconcileWithSchemaWalker`): `optU` with itself and
with nil, the empty child set's `reconOut`.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB2
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSimpArgs false

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace LawB

theorem optU_none_r (x : Option PathSet) : optU x none = x := by cases x <;> rfl

/-- An accumulator unioned with itself is unchanged (as `optU x none`). -/
theorem optU_self (x : Option PathSet) : optU x x = optU x none := by
  have h := optU_idem_law_holds x none
  rw [optU_none_r] at h
  rw [h, optU_none_r]

theorem atomicNodes_empty (S : Schema) (t : TypeRef) :
    (atomicNodes S t PathSet.empty).isEmpty = true := rfl

/-- No child set (nil `fieldSet`) and not touched: nothing to add. -/
theorem reconOut_empty (S : Schema) (t : TypeRef) (p : Path) (b : Bool)
    (h : reconTouch S t b PathSet.empty = false) : reconOut S t p b PathSet.empty = none := by
  rw [reconOut_granular_law_holds S t p b _ h]
  simp [reconBelow, atomicNodes_empty]

/-- A schema in scope never names the reserved `__untyped_deduced_` (a map's element type resolves). -/
theorem find_not_untyped (S : Schema) (hS : S.WF) (n : GoString) (a : Atom) (h : S.find n = some a) :
    n ≠ go!"__untyped_deduced_" := by
  intro hn
  subst hn
  have hm := lkv_mem h
  have hmem : go!"__untyped_deduced_" ∈ S.types.map (·.1) := List.mem_map.2 ⟨_, hm, rfl⟩
  unfold Schema.WF at hS
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hS
  have h2 := hS.1.2
  rw [List.contains_iff_mem.2 hmem] at h2
  exact absurd h2 (by decide)

/-- A map type's element type is never the reserved `__untyped_deduced_` in a schema in scope:
`isUntypedDeducedMap` is false. -/
theorem map_elem_not_untyped (S : Schema) (hS : S.WF) (n : GoString) (fs : List (GoString × TypeRef))
    (e : Option TypeRef) (rel : ElemRel) (h : S.find n = some (.map fs e rel)) :
    e.map (·.name) ≠ some go!"__untyped_deduced_" := by
  rcases e with _ | t
  · simp
  · have hw := find_wf S hS _ _ h
    have hres : S.resolves t = true := by
      simp only [Atom.wf, Bool.and_eq_true] at hw; exact hw.2
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hres
    simp only [Option.map_some, ne_eq, Option.some.injEq]
    exact find_not_untyped S hS _ _ ha

/-! ## The compare walker's node change (`compare`'s tail) -/

theorem cmp_node_added (C B : Cmp) (p : Path) (r : Option UVal) :
    C.union (B.union (nodeC p none r)) =
      ⟨(C.union B).removed, (C.union B).modified, ((C.union B).added).union (ins p)⟩ := by
  simp only [Cmp.union, nodeC, Cmp.none, PathSet.union, PathSet.empty, fset_union_assoc, fset_union_empty]

theorem cmp_node_removed (C B : Cmp) (p : Path) (x : UVal) :
    C.union (B.union (nodeC p (some x) none)) =
      ⟨((C.union B).removed).union (ins p), (C.union B).modified, (C.union B).added⟩ := by
  simp only [Cmp.union, nodeC, Cmp.none, PathSet.union, PathSet.empty, fset_union_assoc, fset_union_empty]

theorem cmp_node_none (C B : Cmp) (p : Path) (x y : UVal) :
    C.union (B.union (nodeC p (some x) (some y))) = C.union B := by
  simp only [Cmp.union, nodeC, Cmp.none, PathSet.union, PathSet.empty, fset_union_assoc, fset_union_empty]

/-! ## An atomic node's own `reconOut` (`doList`/`doMap`'s granular-to-atomic branch) -/

/-- Nothing below a non-granular node is reached by the walker: no atomic nodes below it. -/
theorem atomicNodes_notGranular (S : Schema) (t : TypeRef) (F : PathSet)
    (h : isGranularT S t = false) : (atomicNodes S t F).isEmpty = true := by
  unfold atomicNodes
  apply fset_filter_false
  intro p
  cases p with
  | nil => rfl
  | cons pe q => simp [reconAt, h]

theorem fset_map_empty {α β : Type} (f : α → β) : FSet.map f FSet.empty = FSet.empty := rfl

/-- An atomic node touched: itself only. -/
theorem reconOut_atomic (S : Schema) (t : TypeRef) (p : Path) (b : Bool) (F : PathSet)
    (h : isGranularT S t = false) (hT : reconTouch S t b F = true) :
    reconOut S t p b F = some (ins p) := by
  unfold reconOut
  rw [fset_isEmpty_eq _ (atomicNodes_notGranular S t F h), hT]
  simp only [Bool.true_or, ↓reduceIte, fset_map_empty]
  exact congrArg some (fset_union_empty _)

/-- An atomic node not touched: nothing. -/
theorem reconOut_atomic_none (S : Schema) (t : TypeRef) (p : Path) (b : Bool) (F : PathSet)
    (h : isGranularT S t = false) (hT : reconTouch S t b F = false) :
    reconOut S t p b F = none := by
  unfold reconOut
  dsimp only
  rw [atomicNodes_notGranular S t F h, hT]
  rfl

theorem dedupL_ne {α : Type} [DecidableEq α] : ∀ (l : List α), l ≠ [] → FSet.dedupL l ≠ []
  | [], h => absurd rfl h
  | x :: xs, _ => by
    unfold FSet.dedupL
    split
    · rename_i hx; exact dedupL_ne xs (List.ne_nil_of_mem hx)
    · simp

/-- A set is non-empty iff it counts at least one. -/
theorem isEmpty_false_iff {α : Type} [DecidableEq α] (s : FSet α) :
    s.isEmpty = false ↔ 0 < s.card := by
  induction s using Quotient.inductionOn with | h l =>
  show (!l.any (fun _ => true)) = false ↔ 0 < (FSet.dedupL l).length
  cases l with
  | nil => simp [FSet.dedupL]
  | cons x xs =>
    simp only [List.any_cons, Bool.true_or, Bool.not_true, true_iff]
    exact List.length_pos_iff.2 (dedupL_ne _ (by simp))

end LawB

end smd
end EtcdGrove
end Perennial
