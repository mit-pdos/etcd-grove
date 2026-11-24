/-
**Pure facts about `computeMemberID`'s values** (claim #34, stage 2, 2026-11-25): Go's string order
(`go.GoStringLe`, `strLeB`) is a total order, so the sorted permutation `sort.Strings` leaves is
`mergeSort strLeB`; `strings.Join(xs, "")` is `flatten`. Lean-first. A defs module.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Build

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

/-! ### Go's string order -/

theorem membership.lexR_irrefl :
    ∀ (l : List w8), ¬ List.Lex (fun x y : w8 => uint.Z x < uint.Z y) l l
  | [], h => by cases h
  | a :: l, h => by
    cases h with
    | cons h => exact membership.lexR_irrefl l h
    | rel h => exact Int.lt_irrefl _ h

theorem membership.lexR_asymm :
    ∀ (a b : List w8), List.Lex (fun x y : w8 => uint.Z x < uint.Z y) a b →
      ¬ List.Lex (fun x y : w8 => uint.Z x < uint.Z y) b a
  | [], _, _, h2 => by cases h2
  | _ :: _, [], h1, _ => by cases h1
  | x :: a, y :: b, h1, h2 => by
    cases h1 with
    | cons h1 =>
      cases h2 with
      | cons h2 => exact membership.lexR_asymm a b h1 h2
      | rel h2 => exact Int.lt_irrefl _ h2
    | rel h1 =>
      cases h2 with
      | cons _ => exact Int.lt_irrefl _ h1
      | rel h2 => exact Int.lt_irrefl _ (Int.lt_trans h1 h2)

theorem membership.lexR_trans :
    ∀ (a b c : List w8), List.Lex (fun x y : w8 => uint.Z x < uint.Z y) a b →
      List.Lex (fun x y : w8 => uint.Z x < uint.Z y) b c →
      List.Lex (fun x y : w8 => uint.Z x < uint.Z y) a c
  | [], _, [], _, h2 => by cases h2
  | [], _, _ :: _, _, _ => List.Lex.nil
  | _ :: _, [], _, h1, _ => by cases h1
  | _ :: _, _ :: _, [], _, h2 => by cases h2
  | x :: a, y :: b, z :: c, h1, h2 => by
    cases h1 with
    | cons h1 =>
      cases h2 with
      | cons h2 => exact List.Lex.cons (membership.lexR_trans a b c h1 h2)
      | rel h2 => exact List.Lex.rel h2
    | rel h1 =>
      cases h2 with
      | cons _ => exact List.Lex.rel h1
      | rel h2 => exact List.Lex.rel (Int.lt_trans h1 h2)

theorem membership.lexR_total :
    ∀ (a b : List w8), a = b ∨ List.Lex (fun x y : w8 => uint.Z x < uint.Z y) a b ∨
      List.Lex (fun x y : w8 => uint.Z x < uint.Z y) b a
  | [], [] => Or.inl rfl
  | [], _ :: _ => Or.inr (Or.inl List.Lex.nil)
  | _ :: _, [] => Or.inr (Or.inr List.Lex.nil)
  | x :: a, y :: b => by
    rcases Int.lt_trichotomy (uint.Z x) (uint.Z y) with h | h | h
    · exact Or.inr (Or.inl (List.Lex.rel h))
    · have hxy : x = y := by word
      subst hxy
      rcases membership.lexR_total a b with h' | h' | h'
      · exact Or.inl (by rw [h'])
      · exact Or.inr (Or.inl (List.Lex.cons h'))
      · exact Or.inr (Or.inr (List.Lex.cons h'))
    · exact Or.inr (Or.inr (List.Lex.rel h))

theorem membership.strLeB_iff (a b : GoString) : membership.strLeB a b = true ↔ go.GoStringLe a b := by
  unfold membership.strLeB; simp

theorem membership.strLeB_trans (a b c : GoString) :
    membership.strLeB a b = true → membership.strLeB b c = true → membership.strLeB a c = true := by
  simp only [membership.strLeB_iff, go.GoStringLe, go.GoStringLt]
  rintro (rfl | h1) (rfl | h2)
  · exact Or.inl rfl
  · exact Or.inr h2
  · exact Or.inr h1
  · exact Or.inr (membership.lexR_trans a b c h1 h2)

theorem membership.strLeB_total (a b : GoString) :
    (membership.strLeB a b || membership.strLeB b a) = true := by
  rw [Bool.or_eq_true, membership.strLeB_iff, membership.strLeB_iff]
  simp only [go.GoStringLe, go.GoStringLt]
  rcases membership.lexR_total a b with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

theorem membership.strLeB_antisymm (a b : GoString) :
    membership.strLeB a b = true → membership.strLeB b a = true → a = b := by
  simp only [membership.strLeB_iff, go.GoStringLe, go.GoStringLt]
  rintro (rfl | h1) (h2 | h2)
  · rfl
  · rfl
  · exact h2.symm
  · exact absurd h2 (membership.lexR_asymm a b h1)

/-! ### A sorted permutation is unique -/

theorem membership.sorted_perm_eq {α : Type} (le : α → α → Bool)
    (antisymm : ∀ a b, le a b = true → le b a = true → a = b) :
    ∀ (l1 l2 : List α), l1.Perm l2 → l1.Pairwise (fun a b => le a b = true) →
      l2.Pairwise (fun a b => le a b = true) → l1 = l2
  | [], _, hp, _, _ => hp.nil_eq
  | _ :: _, [], hp, _, _ => by simp at hp
  | a :: t1, b :: t2, hp, h1, h2 => by
    have ha : a ∈ b :: t2 := hp.subset List.mem_cons_self
    have hb : b ∈ a :: t1 := hp.symm.subset List.mem_cons_self
    have hab : a = b := by
      rcases List.mem_cons.1 ha with h | h
      · exact h
      · rcases List.mem_cons.1 hb with h' | h'
        · exact h'.symm
        · exact antisymm a b (List.rel_of_pairwise_cons h1 h') (List.rel_of_pairwise_cons h2 h)
    subst hab
    rw [membership.sorted_perm_eq le antisymm t1 t2 ((List.perm_cons a).1 hp) h1.tail h2.tail]

/-- **`sort.Strings`' answer is `mergeSort strLeB`**: a permutation of `xs` sorted by Go's order. -/
theorem membership.sortStrings_eq (xs xs' : List GoString) (hp : xs.Perm xs')
    (hs : ∀ (i j : Nat) (xi xj : GoString), xs'[i]? = some xi → xs'[j]? = some xj → i < j →
      go.GoStringLe xi xj) :
    xs' = xs.mergeSort membership.strLeB := by
  apply membership.sorted_perm_eq membership.strLeB membership.strLeB_antisymm
  · exact hp.symm.trans (List.mergeSort_perm xs _).symm
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [membership.strLeB_iff]
    exact hs i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
  · exact List.pairwise_mergeSort membership.strLeB_trans membership.strLeB_total xs

/-- `strings.Join(xs, "")` is the concatenation. -/
theorem membership.intercalate_empty (xs : List GoString) :
    ([] : GoString).intercalate xs = xs.flatten := by
  induction xs with
  | nil => rfl
  | cons x t ih =>
    cases t with
    | nil => simp
    | cons y t => rw [List.intercalate_cons_cons, ih]; simp

end EtcdGrove
end Perennial
