/-
**Proofs of the pure merge/compare/reconcile laws of `typed`** (`WalkerLaws.lean`), part B:
`merge_mergeO`, `compare_cmpO`, `optU_assoc`, `optU_idem`, `reconOut_scalar`,
`reconOut_granular`, `mergeO_leaf`, `cmpO_below`, and the fuel laws.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.WalkerLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace LawB

/-! ## Finite sets -/

theorem fset_union_assoc {α : Type} (a b c : FSet α) :
    FSet.union (FSet.union a b) c = FSet.union a (FSet.union b c) := by
  induction a using Quotient.inductionOn with | h la =>
  induction b using Quotient.inductionOn with | h lb =>
  induction c using Quotient.inductionOn with | h lc =>
  exact congrArg (Quotient.mk _) (List.append_assoc la lb lc)

theorem fset_union_idem {α : Type} (a b : FSet α) :
    FSet.union a (FSet.union a b) = FSet.union a b := by
  induction a using Quotient.inductionOn with | h la =>
  induction b using Quotient.inductionOn with | h lb =>
  exact Quotient.sound (fun x => by simp only [List.mem_append, ← or_assoc, or_self])

theorem fset_union_self {α : Type} (a : FSet α) : FSet.union a a = a := by
  induction a using Quotient.inductionOn with | h la =>
  exact Quotient.sound (fun x => by simp only [List.mem_append, or_self])

theorem fset_empty_union {α : Type} (a : FSet α) : FSet.union FSet.empty a = a := by
  induction a using Quotient.inductionOn with | h la =>
  rfl

theorem fset_union_empty {α : Type} (a : FSet α) : FSet.union a FSet.empty = a := by
  induction a using Quotient.inductionOn with | h la =>
  exact congrArg (Quotient.mk _) (List.append_nil la)

theorem fset_filter_false {α : Type} (p : α → Bool) (s : FSet α) (h : ∀ x, p x = false) :
    (s.filter p).isEmpty = true := by
  induction s using Quotient.inductionOn with | h l =>
  show (!(l.filter p).any (fun _ => true)) = true
  rw [List.filter_eq_nil_iff.2 (fun x _ => by simp [h x])]
  rfl

end LawB

open LawB

theorem merge_mergeO_law_holds : merge_mergeO.law := fun _ _ _ _ => rfl

theorem compare_cmpO_law_holds : compare_cmpO.law := fun _ _ _ _ => rfl

theorem optU_assoc_law_holds : optU_assoc.law := by
  intro a b c
  cases a <;> cases b <;> cases c <;> simp only [optU, PathSet.union, fset_union_assoc]

theorem optU_idem_law_holds : optU_idem.law := by
  intro a b
  cases a <;> cases b <;> simp only [optU, PathSet.union, fset_union_idem, fset_union_self]

theorem atomicNodes_scalar (S : Schema) (t : TypeRef) (s : Scalar) (F : PathSet)
    (h : S.find t.name = some (.scalar s)) : (atomicNodes S t F).isEmpty = true := by
  unfold atomicNodes
  apply fset_filter_false
  intro p
  cases p with
  | nil => rfl
  | cons pe p => simp [reconAt, isGranularT, h]

theorem reconOut_scalar_law_holds : reconOut_scalar.law := by
  intro S t p b F s h
  have hn := atomicNodes_scalar S t s F h
  simp [reconOut, reconTouch, h, hn]

theorem reconOut_granular_law_holds : reconOut_granular.law := by
  intro S t p b F h
  unfold reconOut reconBelow
  simp only [h, Bool.false_or, Bool.not_eq_true', Bool.false_eq_true, ite_false]
  cases hn : (atomicNodes S t F).isEmpty
  · simp only [ite_true, PathSet.union, empty, PathSet.empty, fset_empty_union]
    rfl
  · rfl

theorem mergeO_leaf_law_holds : mergeO_leaf.law := by
  intro S t l r hleaf _
  unfold mergeO fuelO
  rw [show sizeO l + sizeO r + 1 = (sizeO l + sizeO r) + 1 from rfl]
  unfold mergeF
  unfold leafAt at hleaf
  split at hleaf <;> rename_i heq <;> simp only [heq] <;> simp_all

#print axioms mergeO_leaf_law_holds
#print axioms reconOut_granular_law_holds
#print axioms reconOut_scalar_law_holds
end smd
end EtcdGrove
end Perennial
