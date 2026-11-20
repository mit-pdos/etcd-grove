/-
Pure helpers of the reconcile walker's proofs (`reconcileWithSchemaWalker`): `optU` with itself and
with nil, the empty child set's `reconOut`.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB2

@[expose] public section

noncomputable section

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

end LawB

end smd
end EtcdGrove
end Perennial
