module
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Model

@[expose] public section

/-! Pure list lemmas for the `items` proofs (`items.removeAt`, `items.find`). -/

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

/-- The list `items.removeAt` leaves: `copy(s[i:], s[i+1:])` shifts the tail left, the last
slot is zeroed and dropped. -/
theorem removeAt_list {A : Type} (vs : List A) (i : Nat) (z : A) (hi : i < vs.length) :
    ((vs.take i ++ ((subslice (i + 1) vs.length vs).take (vs.length - i) ++
        (subslice i vs.length vs).drop (vs.length - (i + 1))) ++ vs.drop vs.length).set
        (vs.length - 1) z).take (vs.length - 1) = vs.take i ++ vs.drop (i + 1) := by
  rw [List.take_set_of_le (Nat.le_refl _)]
  simp only [List.drop_length, List.append_nil, subslice, List.take_length]
  rw [List.take_of_length_le (l := vs.drop (i + 1)) (by simp; omega), ← List.append_assoc]
  exact List.take_left' (by simp; omega)

section find
variable {V K : Type} (lt : K → K → Prop)

/-- The predicate `items.find` passes to `sort.Search`: `less(item, s[i])`, on the key
`k` of `item` (true out of bounds, where `sort.Search` never calls it). -/
def findPred (is : List (V × K)) (k : K) : Int → Bool :=
  open Classical in
  fun i => match is[i.toNat]? with
    | some e => decide (lt k e.2)
    | none => true

theorem findPred_eq (is : List (V × K)) (k : K) (i : Int) (e : V × K)
    (h : is[i.toNat]? = some e) : findPred lt is k i = true ↔ lt k e.2 := by
  unfold findPred; rw [h]; simp

theorem sorted_lt_getElem {l : List (V × K)} (hs : Sorted lt l) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) (hij : i < j) : lt l[i].2 l[j].2 :=
  List.pairwise_iff_getElem.mp hs i j hi hj hij

theorem countLt_eq (is : List (V × K)) (k : K) (m : Nat) (hm : m ≤ is.length)
    (hlt : ∀ j (h : j < m), lt (is[j]'(by omega)).2 k)
    (hge : ∀ (h : m < is.length), ¬ lt is[m].2 k) : countLt lt is k = m := by
  induction is generalizing m with
  | nil => simp [countLt] at hm ⊢; omega
  | cons x xs ih =>
    unfold countLt
    cases m with
    | zero =>
      have := hge (by simp)
      simp only [List.getElem_cons_zero] at this
      simp [this]
    | succ m =>
      have hx := hlt 0 (by omega)
      simp only [List.getElem_cons_zero] at hx
      have := ih m (by simp at hm; omega) (fun j h => by
          have := hlt (j + 1) (by omega); simpa using this)
        (fun h => by have := hge (by simp; omega); simpa using this)
      unfold countLt at this
      simp [hx, this]

/-- What `items.find` computes from `sort.Search`'s result `i` (the first index whose key
is above `k`): the index and `found`, in its two cases. -/
theorem find_found (ho : StrictOrder lt) (is : List (V × K)) (k : K) (hs : Sorted lt is)
    (i : Nat) (hi : i ≤ is.length) (hpos : 0 < i)
    (hbelow : ∀ j (h : j < i), ¬ lt k (is[j]'(by omega)).2)
    (hnot : ¬ lt (is[i - 1]'(by omega)).2 k) :
    countLt lt is k = i - 1 ∧ ∃ e, is[i - 1]? = some e ∧ e.2 = k := by
  have heq : (is[i - 1]'(by omega)).2 = k := by
    rcases ho.total (is[i - 1]'(by omega)).2 k with h | h | h
    · exact absurd h hnot
    · exact h
    · exact absurd h (hbelow (i - 1) (by omega))
  refine ⟨countLt_eq lt is k (i - 1) (by omega) (fun j h => ?_) (fun h => ?_), _,
    List.getElem?_eq_getElem (by omega), heq⟩
  · rw [← heq]; exact sorted_lt_getElem lt hs _ _ h
  · rw [heq]; exact ho.irrefl k

theorem find_notfound (ho : StrictOrder lt) (is : List (V × K)) (k : K) (hs : Sorted lt is)
    (i : Nat) (hi : i ≤ is.length)
    (habove : ∀ (h : i < is.length), lt k is[i].2)
    (hprev : ∀ (h : 0 < i), lt (is[i - 1]'(by omega)).2 k) :
    countLt lt is k = i ∧ ¬ ∃ e, is[i]? = some e ∧ e.2 = k := by
  refine ⟨countLt_eq lt is k i hi (fun j h => ?_) (fun h => ?_), ?_⟩
  · have hp := hprev (by omega)
    by_cases hj : j = i - 1
    · subst hj; exact hp
    · exact ho.trans _ _ _ (sorted_lt_getElem lt hs _ _ (by omega)) hp
  · intro h'; exact ho.irrefl _ (ho.trans _ _ _ h' (habove h))
  · rintro ⟨e, he, rfl⟩
    rcases List.getElem?_eq_some_iff.mp he with ⟨h, rfl⟩
    exact ho.irrefl _ (habove h)

end find

end btree
end EtcdGrove
end Perennial
