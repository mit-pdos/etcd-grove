/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Sorting.lean`, run `rabia-r1wake-1`.)

Pure lemmas of the ledger's tally order: `tallyLt` is a strict weak order, total on tallies of
distinct ids, and any sorted permutation of tallies of distinct ids is `sortProps` of them.
-/
module

public import Dsverify.Proof.rabia.internal.ledger.Spec
public import Perennial.Proof.sort.SorterBasics
import all Init.Data.List.Sort.Basic

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.ledger

open model

theorem tallyLt_iff (a b : ObjV × Nat) :
    tallyLt a b = true ↔ (a.2 > b.2 ∨ (a.2 = b.2 ∧ (a.1.proSeq.toNat < b.1.proSeq.toNat ∨
      (a.1.proSeq.toNat = b.1.proSeq.toNat ∧ a.1.proId.toNat < b.1.proId.toNat)))) := by
  unfold tallyLt
  have h : a.1.proSeq = b.1.proSeq ↔ a.1.proSeq.toNat = b.1.proSeq.toNat :=
    ⟨fun h => by rw [h], fun h => BitVec.eq_of_toNat_eq h⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, h]

theorem sameId_false_iff (a b : ObjV) :
    a.sameId b = false ↔ ¬ (a.proSeq.toNat = b.proSeq.toNat ∧ a.proId.toNat = b.proId.toNat) := by
  unfold ObjV.sameId
  have h1 : a.proSeq = b.proSeq ↔ a.proSeq.toNat = b.proSeq.toNat :=
    ⟨fun h => by rw [h], fun h => BitVec.eq_of_toNat_eq h⟩
  have h2 : a.proId = b.proId ↔ a.proId.toNat = b.proId.toNat :=
    ⟨fun h => by rw [h], fun h => BitVec.eq_of_toNat_eq h⟩
  simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, h1, h2]
  constructor
  · rintro (h | h) ⟨h', h''⟩ <;> contradiction
  · intro h
    by_cases h' : a.proSeq.toNat = b.proSeq.toNat
    · exact Or.inr (fun h'' => h ⟨h', h''⟩)
    · exact Or.inl h'

theorem tallyLt_irrefl (a : ObjV × Nat) : ¬ tallyLt a a = true := by
  rw [tallyLt_iff]; omega

theorem tallyLt_trans (a b c : ObjV × Nat) :
    tallyLt a b = true → tallyLt b c = true → tallyLt a c = true := by
  simp only [tallyLt_iff]; omega

theorem tallyLt_asymm (a b : ObjV × Nat) : tallyLt a b = true → ¬ tallyLt b a = true := by
  simp only [tallyLt_iff]; omega

theorem tallyLt_total (a b : ObjV × Nat) (h : a.1.sameId b.1 = false) :
    tallyLt a b = true ∨ tallyLt b a = true := by
  rw [sameId_false_iff] at h
  simp only [tallyLt_iff]; omega

theorem tallyLt_swo : slices.StrictWeakOrder (fun a b : ObjV × Nat => tallyLt a b = true) where
  strict_weak_order_irrefl := tallyLt_irrefl
  strict_weak_order_trans := tallyLt_trans
  strict_weak_order_equiv := by
    constructor
    · intro x; exact ⟨tallyLt_irrefl x, tallyLt_irrefl x⟩
    · intro x y h; exact ⟨h.2, h.1⟩
    · intro x y z h1 h2
      simp only [tallyLt_iff] at *
      omega

/-! ### `mergeSort` on lists whose distinct positions are comparable -/

section merge
variable {α : Type} (lt : α → α → Bool)

theorem pairwise_merge_of_cmp (trans : ∀ a b c, lt a b → lt b c → lt a c)
    (l₁ l₂ : List α) (h₁ : l₁.Pairwise (fun a b => lt a b)) (h₂ : l₂.Pairwise (fun a b => lt a b))
    (hc : ∀ a ∈ l₁, ∀ b ∈ l₂, lt a b ∨ lt b a) :
    (List.merge l₁ l₂ lt).Pairwise (fun a b => lt a b) := by
  induction l₁ generalizing l₂ with
  | nil => simpa only [List.merge]
  | cons x l₁ ih₁ =>
    induction l₂ with
    | nil => simpa only [List.merge]
    | cons y l₂ ih₂ =>
      simp only [List.merge]
      split <;> rename_i h
      · apply List.Pairwise.cons
        · intro z m
          rw [List.mem_merge, List.mem_cons] at m
          rcases m with (m|rfl|m)
          · exact List.rel_of_pairwise_cons h₁ m
          · exact h
          · exact trans _ _ _ h (List.rel_of_pairwise_cons h₂ m)
        · exact ih₁ _ h₁.tail h₂ (fun a ha b hb => hc a (List.mem_cons_of_mem _ ha) b hb)
      · have hyx : lt y x := by
          rcases hc x List.mem_cons_self y List.mem_cons_self with h' | h'
          · exact absurd h' h
          · exact h'
        apply List.Pairwise.cons
        · intro z m
          rw [List.mem_merge, List.mem_cons] at m
          rcases m with (⟨rfl|m⟩|m)
          · exact hyx
          · exact trans _ _ _ hyx (List.rel_of_pairwise_cons h₁ m)
          · exact List.rel_of_pairwise_cons h₂ m
        · exact ih₂ h₂.tail (fun a ha b hb => hc a ha b (List.mem_cons_of_mem _ hb))

theorem pairwise_mergeSort_of_cmp (trans : ∀ a b c, lt a b → lt b c → lt a c) :
    (l : List α) → l.Pairwise (fun a b => lt a b ∨ lt b a) →
      (List.mergeSort l lt).Pairwise (fun a b => lt a b)
  | [], _ => by simp
  | [a], _ => by simp
  | a :: b :: xs, hl => by
    rw [List.mergeSort]
    have e := List.MergeSort.Internal.splitInTwo_fst_append_splitInTwo_snd
      (⟨a :: b :: xs, rfl⟩ : { l : List α // l.length = (a :: b :: xs).length })
    have hl' : List.Pairwise (fun a b => lt a b = true ∨ lt b a = true)
        ((List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).1.1 ++
          (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).2.1) := by
      rw [e]; exact hl
    rw [List.pairwise_append] at hl'
    have : (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).1.1.length < xs.length + 1 + 1 := by
      simp [List.MergeSort.Internal.splitInTwo_fst]; omega
    have : (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).2.1.length < xs.length + 1 + 1 := by
      simp [List.MergeSort.Internal.splitInTwo_snd]; omega
    apply pairwise_merge_of_cmp lt trans
    · exact pairwise_mergeSort_of_cmp trans _ hl'.1
    · exact pairwise_mergeSort_of_cmp trans _ hl'.2.1
    · intro x hx y hy
      rw [List.mem_mergeSort] at hx hy
      exact hl'.2.2 x hx y hy
termination_by l => l.length

/-- Two permutations of each other, both strictly sorted by an asymmetric relation, are equal. -/
theorem eq_of_perm_of_pairwise_asymm (asymm : ∀ a b, lt a b → ¬ lt b a) :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.Pairwise (fun a b => lt a b) →
      l₂.Pairwise (fun a b => lt a b) → l₁ = l₂
  | [], l₂, hp, _, _ => (List.Perm.nil_eq hp)
  | a :: t₁, [], hp, _, _ => absurd hp.length_eq (by simp)
  | a :: t₁, b :: t₂, hp, h₁, h₂ => by
    have hab : a = b := by
      apply Classical.byContradiction; intro hne
      have ha : a ∈ b :: t₂ := hp.subset List.mem_cons_self
      have hb : b ∈ a :: t₁ := hp.symm.subset List.mem_cons_self
      rcases List.mem_cons.1 ha with h | ha
      · exact hne h
      rcases List.mem_cons.1 hb with h | hb
      · exact hne h.symm
      exact asymm _ _ (List.rel_of_pairwise_cons h₁ hb) (List.rel_of_pairwise_cons h₂ ha)
    subst hab
    rw [eq_of_perm_of_pairwise_asymm asymm (List.Perm.cons_inv hp) h₁.tail h₂.tail]

end merge

/-- Tallies of distinct ids. -/
abbrev distinctIds (xs : List (ObjV × Nat)) : Prop :=
  (xs.map Prod.fst).Pairwise (fun a b => a.sameId b = false)

theorem distinctIds_iff (xs : List (ObjV × Nat)) :
    distinctIds xs ↔ xs.Pairwise (fun a b => a.1.sameId b.1 = false) := by
  unfold distinctIds; rw [List.pairwise_map]

theorem sameId_comm (a b : ObjV) : a.sameId b = b.sameId a := by
  unfold ObjV.sameId
  rw [Bool.beq_comm (a := a.proSeq), Bool.beq_comm (a := a.proId)]

theorem distinctIds_perm {xs ys : List (ObjV × Nat)} (h : distinctIds xs) (hp : xs.Perm ys) :
    distinctIds ys := by
  rw [distinctIds_iff] at *
  exact h.perm hp (fun h => by rw [sameId_comm]; exact h)

theorem sortProps_pairwise (xs : List (ObjV × Nat)) (h : distinctIds xs) :
    (sortProps xs).Pairwise (fun a b => tallyLt a b) := by
  unfold sortProps
  apply pairwise_mergeSort_of_cmp tallyLt tallyLt_trans
  rw [distinctIds_iff] at h
  exact h.imp (fun h' => tallyLt_total _ _ h')

/-- **A sorted permutation of tallies of distinct ids is `sortProps` of them.** -/
theorem sortProps_eq (xs ys : List (ObjV × Nat)) (hd : distinctIds xs) (hp : xs.Perm ys)
    (hs : ∀ (i j : Nat) (xi xj : ObjV × Nat), ys[i]? = some xi → ys[j]? = some xj → i < j →
      ¬ tallyLt xj xi = true) :
    sortProps xs = ys := by
  have hdy := distinctIds_perm hd hp
  rw [distinctIds_iff] at hdy
  have hys : ys.Pairwise (fun a b => tallyLt a b) := by
    rw [List.pairwise_iff_getElem] at hdy ⊢
    intro i j hi hj hij
    rcases tallyLt_total _ _ (hdy i j hi hj hij) with h | h
    · exact h
    · exact absurd h (hs i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij)
  exact eq_of_perm_of_pairwise_asymm tallyLt tallyLt_asymm
    ((List.mergeSort_perm xs tallyLt).trans hp) (sortProps_pairwise xs hd) hys

end Perennial.rabia.internal.ledger
