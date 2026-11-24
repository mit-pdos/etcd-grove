/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureL/Sort.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L: generic facts about `List.mergeSort` with a total preorder (Boolean comparator), used by
F2 (`lin_prefix`) and F4 (`lin_congr`).
-/
module

public import Dsverify.Proof.gryff.Proto.Model

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureL

/-- Two sorts of the same list by comparators that are total preorders, agree on the list's
elements, and are antisymmetric on them, are equal. -/
theorem mergeSort_congr {α : Type} {L : List α} {le1 le2 : α → α → Bool}
    (tr1 : ∀ a b c, le1 a b → le1 b c → le1 a c) (to1 : ∀ a b, le1 a b || le1 b a)
    (tr2 : ∀ a b c, le2 a b → le2 b c → le2 a c) (to2 : ∀ a b, le2 a b || le2 b a)
    (hag : ∀ a ∈ L, ∀ b ∈ L, le1 a b = le2 a b)
    (hanti : ∀ a ∈ L, ∀ b ∈ L, le2 a b → le2 b a → a = b) :
    L.mergeSort le1 = L.mergeSort le2 := by
  apply List.Perm.eq_of_pairwise (le := fun a b => le2 a b = true)
  · intro a b ha hb h1 h2
    exact hanti a ((List.mergeSort_perm L le1).subset ha) b
      ((List.mergeSort_perm L le2).subset hb) h1 h2
  · have h := List.pairwise_mergeSort tr1 to1 L
    refine h.imp_of_mem ?_
    intro a b ha hb hab
    rw [← hag a ((List.mergeSort_perm L le1).subset ha) b ((List.mergeSort_perm L le1).subset hb)]
    exact hab
  · exact List.pairwise_mergeSort tr2 to2 L
  · exact (List.mergeSort_perm L le1).trans (List.mergeSort_perm L le2).symm

/-- A sort of a list that is a permutation of `A ++ B`, every element of `B` strictly after every
element of `A`, is the sort of `A` followed by the sort of `B`. -/
theorem mergeSort_append_of_lt {α : Type} {L A B : List α} {le : α → α → Bool}
    (tr : ∀ a b c, le a b → le b c → le a c) (to : ∀ a b, le a b || le b a)
    (hanti : ∀ a ∈ L, ∀ b ∈ L, le a b → le b a → a = b)
    (hp : L.Perm (A ++ B)) (hab : ∀ a ∈ A, ∀ b ∈ B, le a b ∧ ¬ le b a) :
    L.mergeSort le = A.mergeSort le ++ B.mergeSort le := by
  apply List.Perm.eq_of_pairwise (le := fun a b => le a b = true)
  · intro a b ha hb h1 h2
    exact hanti a ((List.mergeSort_perm L le).subset ha) b
      (hp.symm.subset (((List.mergeSort_perm A le).append (List.mergeSort_perm B le)).subset hb))
      h1 h2
  · exact List.pairwise_mergeSort tr to L
  · rw [List.pairwise_append]
    refine ⟨List.pairwise_mergeSort tr to A, List.pairwise_mergeSort tr to B, ?_⟩
    intro a ha b hb
    exact (hab a ((List.mergeSort_perm A le).subset ha) b ((List.mergeSort_perm B le).subset hb)).1
  · exact (List.mergeSort_perm L le).trans
      (hp.trans ((List.mergeSort_perm A le).append (List.mergeSort_perm B le)).symm)

/-- `filterMap` over `range n` ignores the indices from `m` on where the function is `none`. -/
theorem filterMap_range_eq {β : Type} {h : Nat → Option β} {m n : Nat} (hmn : m ≤ n)
    (hn : ∀ g, m ≤ g → h g = none) :
    (List.range n).filterMap h = (List.range m).filterMap h := by
  induction n with
  | zero => have : m = 0 := by omega
            subst this; rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hmn with e | lt
    · rw [e]
    · rw [List.range_succ, List.filterMap_append, ih (by omega)]
      simp [hn n (by omega)]

open Perennial.gryff.proto in
/-- The lexicographic order of `lin`: by tag, then rank, then creation. -/
def lexB (ta tb : PTag) (ra rb ga gb : Nat) : Bool :=
  decide (tagLt ta tb) ||
    (decide (ta = tb) && (decide (ra < rb) || (decide (ra = rb) && decide (ga ≤ gb))))

open Perennial.gryff.proto in
theorem lexB_iff (ta tb : PTag) (ra rb ga gb : Nat) : lexB ta tb ra rb ga gb = true ↔
    (ta.1 < tb.1 ∨ (ta.1 = tb.1 ∧ (ta.2.1 < tb.2.1 ∨ (ta.2.1 = tb.2.1 ∧ ta.2.2 < tb.2.2)))) ∨
    ((ta.1 = tb.1 ∧ ta.2.1 = tb.2.1 ∧ ta.2.2 = tb.2.2) ∧ (ra < rb ∨ (ra = rb ∧ ga ≤ gb))) := by
  obtain ⟨a1, a2, a3⟩ := ta; obtain ⟨b1, b2, b3⟩ := tb
  simp only [lexB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Prod.mk.injEq]
  unfold tagLt; exact Iff.rfl

theorem lexB_total (ta tb : Perennial.gryff.proto.PTag) (ra rb ga gb : Nat) :
    lexB ta tb ra rb ga gb || lexB tb ta rb ra gb ga := by
  rw [Bool.or_eq_true, lexB_iff, lexB_iff]; omega

theorem lexB_trans {ta tb tc : Perennial.gryff.proto.PTag} {ra rb rc ga gb gc : Nat} :
    lexB ta tb ra rb ga gb → lexB tb tc rb rc gb gc → lexB ta tc ra rc ga gc := by
  rw [lexB_iff, lexB_iff, lexB_iff]; omega

theorem lexB_antisymm {ta tb : Perennial.gryff.proto.PTag} {ra rb ga gb : Nat} :
    lexB ta tb ra rb ga gb → lexB tb ta rb ra gb ga → ga = gb := by
  rw [lexB_iff, lexB_iff]; omega

end Perennial.gryff.pureL
