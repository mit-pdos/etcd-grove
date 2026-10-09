/-
Lemmas for the read-only operations (`get`, `min`, `max`, `iterate` and the methods
built on them): lookup and ranges in a node's in-order contents, and read access to a
node (owned or frozen).
-/

module
public import Proof.k8s_io.utils.third_party.forked.golang.btree.NodeLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree
open Classical

/-! ## Pure facts -/

section pure
variable {V K : Type} {lt : K → K → Prop}

/-! ### Sorted lists -/

theorem sorted_cons_iff (x : V × K) (l : List (V × K)) :
    Sorted lt (x :: l) ↔ (∀ e ∈ l, lt x.2 e.2) ∧ Sorted lt l := List.pairwise_cons

theorem sorted_append_iff (l1 l2 : List (V × K)) :
    Sorted lt (l1 ++ l2) ↔ Sorted lt l1 ∧ Sorted lt l2 ∧ ∀ a ∈ l1, ∀ b ∈ l2, lt a.2 b.2 :=
  List.pairwise_append

theorem Sorted.sublist {l1 l2 : List (V × K)} (h : l1.Sublist l2) (hs : Sorted lt l2) :
    Sorted lt l1 := List.Pairwise.sublist h hs

/-- In a sorted `A ++ x :: B`, `A` is below `x` and `B` above. -/
theorem sorted_mid {A B : List (V × K)} {x : V × K} (hs : Sorted lt (A ++ x :: B)) :
    (∀ e ∈ A, lt e.2 x.2) ∧ (∀ e ∈ B, lt x.2 e.2) := by
  rw [sorted_append_iff] at hs
  obtain ⟨_, hB, hAB⟩ := hs
  rw [sorted_cons_iff] at hB
  exact ⟨fun e he => hAB e he x (by simp), hB.1⟩

/-! ### Lookup -/

theorem lookup_cons (x : V × K) (l : List (V × K)) (k : K) :
    lookup (x :: l) k = if x.2 = k then some x.1 else lookup l k := by
  unfold lookup
  by_cases h : x.2 = k <;> simp [h]

theorem lookup_append (l1 l2 : List (V × K)) (k : K) :
    lookup (l1 ++ l2) k = (lookup l1 k).or (lookup l2 k) := by
  unfold lookup
  rw [List.find?_append]
  cases List.find? _ l1 <;> simp

theorem lookup_none_of (l : List (V × K)) (k : K) (h : ∀ e ∈ l, e.2 ≠ k) :
    lookup l k = none := by
  unfold lookup
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro e he
  simpa using h e he

theorem lookup_of_mem (ho : StrictOrder lt) :
    ∀ {l : List (V × K)}, Sorted lt l → ∀ {e : V × K}, e ∈ l → lookup l e.2 = some e.1
  | [], _, _, he => by simp at he
  | x :: l, hs, e, he => by
    rw [sorted_cons_iff] at hs
    rw [lookup_cons]
    rcases List.mem_cons.1 he with rfl | he
    · simp
    · have hne : x.2 ≠ e.2 := fun h => ho.irrefl _ (h ▸ hs.1 e he)
      simp only [hne, ↓reduceIte]
      exact lookup_of_mem ho hs.2 he

/-! ### Ranges -/

theorem ascRange_append (l1 l2 : List (V × K)) (a b : Option K) :
    ascRange lt (l1 ++ l2) a b = ascRange lt l1 a b ++ ascRange lt l2 a b := by
  unfold ascRange; rw [List.filter_append]

theorem descRange_append (l1 l2 : List (V × K)) (a b : Option K) :
    descRange lt (l1 ++ l2) a b = descRange lt l2 a b ++ descRange lt l1 a b := by
  unfold descRange; rw [List.filter_append, List.reverse_append]

theorem ascRange_cons (x : V × K) (l : List (V × K)) (a b : Option K) :
    ascRange lt (x :: l) a b =
      (if ascIn lt a b x.2 then [x] else []) ++ ascRange lt l a b := by
  unfold ascRange; by_cases h : ascIn lt a b x.2 <;> simp [h]

theorem descRange_cons (x : V × K) (l : List (V × K)) (a b : Option K) :
    descRange lt (x :: l) a b =
      descRange lt l a b ++ (if descIn lt a b x.2 then [x] else []) := by
  unfold descRange; by_cases h : descIn lt a b x.2 <;> simp [h]

theorem ascRange_nil_of (l : List (V × K)) (a b : Option K)
    (h : ∀ e ∈ l, ¬ ascIn lt a b e.2) : ascRange lt l a b = [] := by
  unfold ascRange; rw [List.filter_eq_nil_iff]; intro e he; simpa using h e he

theorem descRange_nil_of (l : List (V × K)) (a b : Option K)
    (h : ∀ e ∈ l, ¬ descIn lt a b e.2) : descRange lt l a b = [] := by
  unfold descRange; rw [List.reverse_eq_nil_iff, List.filter_eq_nil_iff]
  intro e he; simpa using h e he

/-! ### `countLt` -/

theorem countLt_le (l : List (V × K)) (k : K) : countLt lt l k ≤ l.length := by
  unfold countLt; exact List.Sublist.length_le (List.takeWhile_sublist _)

theorem lt_of_lt_countLt :
    ∀ (l : List (V × K)) (k : K) (i : Nat) (x : V × K), i < countLt lt l k →
      l[i]? = some x → lt x.2 k
  | [], _, _, _, h, _ => by simp [countLt] at h
  | y :: l, k, i, x, h, hx => by
    unfold countLt at h
    by_cases hy : lt y.2 k
    · rw [List.takeWhile_cons_of_pos (by simpa using hy)] at h
      cases i with
      | zero => simp at hx; subst hx; exact hy
      | succ i =>
        simp at hx
        exact lt_of_lt_countLt l k i x (by simp at h; unfold countLt; omega) hx
    · rw [List.takeWhile_cons_of_neg (by simpa using hy)] at h
      simp at h

theorem not_lt_of_countLt_le (ho : StrictOrder lt) :
    ∀ (l : List (V × K)) (k : K) (i : Nat) (x : V × K), Sorted lt l → countLt lt l k ≤ i →
      l[i]? = some x → ¬ lt x.2 k
  | [], _, _, _, _, _, hx => by simp at hx
  | y :: l, k, i, x, hs, h, hx => by
    rw [sorted_cons_iff] at hs
    unfold countLt at h
    by_cases hy : lt y.2 k
    · rw [List.takeWhile_cons_of_pos (by simpa using hy)] at h
      cases i with
      | zero => simp at h
      | succ i =>
        simp at hx
        exact not_lt_of_countLt_le ho l k i x hs.2 (by simp at h; unfold countLt; omega) hx
    · cases i with
      | zero => simp at hx; subst hx; exact hy
      | succ i =>
        simp at hx
        intro hxk
        exact hy (ho.trans _ _ _ (hs.1 x (List.mem_of_getElem? hx)) hxk)

/-! ### A node's contents, piece by piece -/

/-- The entries of a node from its item `j` on, without child `j`: `xⱼ cⱼ₊₁ xⱼ₊₁ … cₙ`
(given the items from `j` and the children from `j + 1`). -/
def itemsFirst : List (V × K) → List (Tree (V × K)) → List (V × K)
  | [], _ => []
  | x :: xs, [] => x :: itemsFirst xs []
  | x :: xs, c :: cs => x :: (c.elems ++ itemsFirst xs cs)

@[simp] theorem itemsFirst_nil_left (cs : List (Tree (V × K))) : itemsFirst [] cs = [] := by
  cases cs <;> rfl

theorem itemsFirst_nil_right : ∀ (xs : List (V × K)), itemsFirst xs [] = xs
  | [] => rfl
  | x :: xs => by rw [itemsFirst, itemsFirst_nil_right xs]

/-- The entries of child `j` (none for a leaf). -/
def chElems (cs : List (Tree (V × K))) (j : Nat) : List (V × K) :=
  match cs[j]? with
  | some c => c.elems
  | none => []

/-- The entries before child `j`: `c₀ x₀ … cⱼ₋₁ xⱼ₋₁`. -/
def preElems (is : List (V × K)) (cs : List (Tree (V × K))) (j : Nat) : List (V × K) :=
  Tree.elemsAux (is.take j) (cs.take j)

/-- The entries after child `j`: `xⱼ cⱼ₊₁ … cₙ`. -/
def sufElems (is : List (V × K)) (cs : List (Tree (V × K))) (j : Nat) : List (V × K) :=
  itemsFirst (is.drop j) (cs.drop (j + 1))

/-- The children of a node are none (a leaf) or one more than its items. -/
def ShapeOk (is : List (V × K)) (cs : List (Tree (V × K))) : Prop :=
  cs = [] ∨ cs.length = is.length + 1

theorem shapeOk_of_shape {d h : Nat} {is : List (V × K)} {cs : List (Tree (V × K))}
    (hs : (Tree.node is cs).Shape d h) : ShapeOk is cs := by
  cases h with
  | zero => left; simpa [Tree.Shape] using hs
  | succ h => right; exact hs.1

theorem elemsAux_first :
    ∀ (is : List (V × K)) (cs : List (Tree (V × K))), ShapeOk is cs →
      Tree.elemsAux is cs = chElems cs 0 ++ itemsFirst is cs.tail
  | is, [], _ => by simp [chElems, itemsFirst_nil_right]
  | [], [c], _ => by simp [chElems]
  | [], _ :: _ :: _, h => by rcases h with h | h <;> simp at h
  | x :: is, [c], h => by rcases h with h | h <;> simp at h
  | x :: is, c :: c1 :: cs, h => by
    have h' : ShapeOk is (c1 :: cs) := by
      right; rcases h with h | h <;> simp at h ⊢; omega
    rw [Tree.elemsAux_cons_cons, elemsAux_first is (c1 :: cs) h']
    simp [chElems, itemsFirst]

theorem elems_decomp :
    ∀ (j : Nat) (is : List (V × K)) (cs : List (Tree (V × K))), ShapeOk is cs → j ≤ is.length →
      Tree.elemsAux is cs = preElems is cs j ++ chElems cs j ++ sufElems is cs j
  | 0, is, cs, h, _ => by
    simp [preElems, sufElems, elemsAux_first is cs h, List.drop_one]
  | j + 1, [], _, _, hj => by simp at hj
  | j + 1, x :: is, [], _, hj => by
    simp [preElems, sufElems, chElems, itemsFirst_nil_right]
  | j + 1, x :: is, c :: cs, h, hj => by
    have h' : ShapeOk is cs := by
      right; rcases h with h | h <;> simp at h ⊢; omega
    have ih := elems_decomp j is cs h' (by simpa using hj)
    simp only [preElems, sufElems, chElems, List.take_succ_cons, List.drop_succ_cons,
      Tree.elemsAux_cons_cons, List.getElem?_cons_succ] at ih ⊢
    rw [ih]; simp

theorem sufElems_succ (is : List (V × K)) (cs : List (Tree (V × K))) (j : Nat)
    (h : ShapeOk is cs) (hj : j < is.length) :
    sufElems is cs j = is[j] :: (chElems cs (j + 1) ++ sufElems is cs (j + 1)) := by
  unfold sufElems chElems
  rw [List.drop_eq_getElem_cons hj]
  rcases h with rfl | h
  · simp [itemsFirst_nil_right]
  · rw [List.drop_eq_getElem_cons (show j + 1 < cs.length by omega)]
    simp [itemsFirst, List.getElem?_eq_getElem (show j + 1 < cs.length by omega)]

theorem sufElems_length (is : List (V × K)) (cs : List (Tree (V × K))) :
    sufElems is cs is.length = [] := by
  simp [sufElems]

theorem preElems_zero (is : List (V × K)) (cs : List (Tree (V × K))) :
    preElems is cs 0 = [] := by
  simp [preElems]

theorem preElems_succ (is : List (V × K)) (cs : List (Tree (V × K))) (j : Nat)
    (h : ShapeOk is cs) (hj : j < is.length) :
    preElems is cs (j + 1) = preElems is cs j ++ chElems cs j ++ [is[j]] := by
  have e1 := elems_decomp j is cs h (by omega)
  have e2 := elems_decomp (j + 1) is cs h hj
  rw [sufElems_succ is cs j h hj] at e1
  rw [e1] at e2
  have : (preElems is cs j ++ chElems cs j ++ [is[j]]) ++
      (chElems cs (j + 1) ++ sufElems is cs (j + 1)) =
      preElems is cs (j + 1) ++ (chElems cs (j + 1) ++ sufElems is cs (j + 1)) := by
    simpa using e2
  exact (List.append_cancel_right this).symm

theorem items_sublist_elemsAux :
    ∀ (is : List (V × K)) (cs : List (Tree (V × K))), is.Sublist (Tree.elemsAux is cs)
  | is, [] => by simp
  | [], _ :: _ => by simp
  | x :: is, c :: cs => by
    rw [Tree.elemsAux_cons_cons]
    exact (List.Sublist.cons_cons x (items_sublist_elemsAux is cs)).trans
      (List.sublist_append_right _ _)

theorem chElems_eq {cs : List (Tree (V × K))} {j : Nat} {c : Tree (V × K)}
    (h : cs[j]? = some c) : chElems cs j = c.elems := by
  simp [chElems, h]

theorem chElems_of_nil (j : Nat) : chElems ([] : List (Tree (V × K))) j = [] := by
  simp [chElems]

/-! ### `get` -/

/-- `get` at a node: the entry at `countLt` is the key's, or the key is in child
`countLt` (none for a leaf). -/
theorem lookup_node_not_found (ho : StrictOrder lt) (is : List (V × K))
    (cs : List (Tree (V × K))) (k : K) (h : ShapeOk is cs)
    (hs : Sorted lt (Tree.elemsAux is cs))
    (hnf : ¬ ∃ e, is[countLt lt is k]? = some e ∧ e.2 = k) :
    lookup (Tree.elemsAux is cs) k = lookup (chElems cs (countLt lt is k)) k := by
  have hj := countLt_le (lt := lt) is k
  have hsi : Sorted lt is := Sorted.sublist (items_sublist_elemsAux is cs) hs
  have hd := elems_decomp _ is cs h hj
  rw [hd, lookup_append, lookup_append]
  have hpre : lookup (preElems is cs (countLt lt is k)) k = none := by
    apply lookup_none_of
    intro e he heq
    -- e is below the last item before `countLt`, which is below `k`
    obtain ⟨j, hj1⟩ : ∃ j, countLt lt is k = j + 1 := by
      cases hc : countLt lt is k with
      | zero => rw [hc, preElems_zero] at he; simp at he
      | succ j => exact ⟨j, rfl⟩
    have hjl : j < is.length := by omega
    rw [hj1, preElems_succ is cs j h hjl] at he
    have hlt : lt is[j].2 k :=
      lt_of_lt_countLt is k j is[j] (by omega) (List.getElem?_eq_getElem hjl)
    have hd' := elems_decomp j is cs h (by omega)
    rw [sufElems_succ is cs j h hjl] at hd'
    rw [hd'] at hs
    have := (sorted_mid (A := preElems is cs j ++ chElems cs j) (by simpa using hs)).1
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with (he | he) | rfl
    · exact ho.irrefl _ (ho.trans _ _ _ (heq ▸ this e (by simp [he])) hlt)
    · exact ho.irrefl _ (ho.trans _ _ _ (heq ▸ this e (by simp [he])) hlt)
    · exact ho.irrefl _ (heq ▸ hlt)
  have hsuf : lookup (sufElems is cs (countLt lt is k)) k = none := by
    apply lookup_none_of
    intro e he heq
    by_cases hjl : countLt lt is k < is.length
    · have hx := not_lt_of_countLt_le ho is k _ is[countLt lt is k] hsi (Nat.le_refl _)
        (List.getElem?_eq_getElem hjl)
      have hne : is[countLt lt is k].2 ≠ k := fun h' =>
        hnf ⟨_, List.getElem?_eq_getElem hjl, h'⟩
      have hkx : lt k is[countLt lt is k].2 := by
        rcases ho.total is[countLt lt is k].2 k with h1 | h1 | h1
        · exact absurd h1 hx
        · exact absurd h1 hne
        · exact h1
      rw [sufElems_succ is cs _ h hjl] at he
      have hd' := elems_decomp _ is cs h hj
      rw [sufElems_succ is cs _ h hjl] at hd'
      rw [hd'] at hs
      have := (sorted_mid (A := preElems is cs _ ++ chElems cs _) (by simpa using hs)).2
      rcases List.mem_cons.1 he with rfl | he
      · exact hne heq
      · exact ho.irrefl _ (ho.trans _ _ _ hkx (heq ▸ this e he))
    · have : countLt lt is k = is.length := by omega
      rw [this, sufElems_length] at he; simp at he
  rw [hpre, hsuf]
  simp

/-! ### `min`, `max` -/

/-- Below a node of height `h + 1` of a B-tree of degree `d ≥ 2`, every child holds an
entry. -/
theorem child_elems_ne_nil {d h : Nat} {is : List (V × K)} {cs : List (Tree (V × K))}
    (hd : 2 ≤ d) (hs : (Tree.node is cs).Shape d (h + 1)) {c : Tree (V × K)} (hc : c ∈ cs) :
    c.elems ≠ [] := by
  have h1 := (hs.2 c hc).1.1
  obtain ⟨is', cs'⟩ := c
  simp only [Tree.items_node] at h1
  intro he
  have hlen : is'.length ≤ 0 := by
    have := (items_sublist_elemsAux is' cs').length_le
    rw [← Tree.elems_node, he] at this
    simpa using this
  omega

theorem head_elemsAux_cons (is : List (V × K)) (c : Tree (V × K)) (cs : List (Tree (V × K)))
    (hne : c.elems ≠ []) : (Tree.elemsAux is (c :: cs)).head? = c.elems.head? := by
  obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hne
  cases is with
  | nil => rw [Tree.elemsAux_nil_cons, hal]; simp
  | cons x is => rw [Tree.elemsAux_cons_cons, hal]; simp

theorem getLast_elemsAux (is : List (V × K)) (cs : List (Tree (V × K)))
    (hl : cs.length = is.length + 1) (c : Tree (V × K)) (hc : cs[is.length]? = some c)
    (hne : c.elems ≠ []) : (Tree.elemsAux is cs).getLast? = c.elems.getLast? := by
  rw [elems_decomp is.length is cs (Or.inr hl) (Nat.le_refl _), sufElems_length,
    List.append_nil, chElems_eq hc]
  obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hne
  rw [hal, List.getLast?_append, List.getLast?_eq_some_getLast (List.cons_ne_nil a l)]
  rfl

/-! ### Iteration -/

theorem not_isEmpty_append {α : Type} (A B : List α) :
    (!(A ++ B).isEmpty) = or (!A.isEmpty) (!B.isEmpty) := by
  cases A <;> cases B <;> simp

section iter
variable (ho : StrictOrder lt) {is : List (V × K)} {cs : List (Tree (V × K))}
  (hok : ShapeOk is cs) (hs : Sorted lt (Tree.elemsAux is cs))
include ho hok hs

omit ho hok hs in
theorem sorted_split {A B : List (V × K)} (h : Sorted lt (A ++ B)) :
    ∀ a ∈ A, ∀ b ∈ B, lt a.2 b.2 := ((sorted_append_iff A B).1 h).2.2

/-- Everything before child `j` (and the child) is below everything after it. -/
theorem lt_pre_ch_suf (j : Nat) (hj : j ≤ is.length) :
    ∀ e ∈ preElems is cs j ++ chElems cs j, ∀ e' ∈ sufElems is cs j, lt e.2 e'.2 := by
  rw [elems_decomp j is cs hok hj] at hs
  exact sorted_split hs

theorem lt_pre_ch_suf' (j : Nat) (hj : j ≤ is.length) :
    ∀ e ∈ preElems is cs j, ∀ e' ∈ chElems cs j ++ sufElems is cs j, lt e.2 e'.2 := by
  rw [elems_decomp j is cs hok hj, List.append_assoc] at hs
  exact sorted_split hs

/-- Item `j` is above everything before it. -/
theorem lt_item (j : Nat) (hj : j < is.length) :
    ∀ e ∈ preElems is cs j ++ chElems cs j, lt e.2 is[j].2 := by
  intro e he
  exact lt_pre_ch_suf ho hok hs j (by omega) e he is[j]
    (by rw [sufElems_succ is cs j hok hj]; simp)

/-- Item `j` is below everything after it. -/
theorem item_lt (j : Nat) (hj : j < is.length) :
    ∀ e ∈ chElems cs (j + 1) ++ sufElems is cs (j + 1), lt is[j].2 e.2 := by
  have h := elems_decomp j is cs hok (by omega)
  rw [sufElems_succ is cs j hok hj] at h
  rw [h] at hs
  exact (sorted_mid hs).2

theorem pre_countLt_lt (a : K) :
    ∀ e ∈ preElems is cs (countLt lt is a), lt e.2 a := by
  intro e he
  obtain ⟨j, hj1⟩ : ∃ j, countLt lt is a = j + 1 := by
    cases hc : countLt lt is a with
    | zero => rw [hc, preElems_zero] at he; simp at he
    | succ j => exact ⟨j, rfl⟩
  have hjl : j < is.length := by have := countLt_le (lt := lt) is a; omega
  have hlt : lt is[j].2 a :=
    lt_of_lt_countLt is a j is[j] (by omega) (List.getElem?_eq_getElem hjl)
  rw [hj1, preElems_succ is cs j hok hjl] at he
  simp only [List.mem_append, List.mem_singleton] at he
  rcases he with (he | he) | rfl
  · exact ho.trans _ _ _ (lt_item ho hok hs j hjl e (by simp [he])) hlt
  · exact ho.trans _ _ _ (lt_item ho hok hs j hjl e (by simp [he])) hlt
  · exact hlt

/-! #### Ascending -/

/-- Where an ascending iteration starts in a node: the first item not below `start`. -/
def ascStart (lt : K → K → Prop) (is : List (V × K)) : Option K → Nat
  | some a => countLt lt is a
  | none => 0

omit ho hok hs in
theorem ascStart_le (ks : Option K) : ascStart lt is ks ≤ is.length := by
  cases ks <;> simp [ascStart, countLt_le]

theorem asc_pre_start (ks ku : Option K) :
    ascRange lt (preElems is cs (ascStart lt is ks)) ks ku = [] := by
  cases ks with
  | none => simp [ascStart, preElems_zero, ascRange]
  | some a =>
    apply ascRange_nil_of
    intro e he hin
    exact hin.1 a rfl (pre_countLt_lt ho hok hs a e he)

omit hok in
theorem ascIn_item (ks ku : Option K) (i : Nat) (hi1 : ascStart lt is ks ≤ i)
    (hi2 : i < is.length) (hstop : ∀ b, ku = some b → lt is[i].2 b) :
    ascIn lt ks ku is[i].2 := by
  refine ⟨?_, hstop⟩
  intro a ha
  subst ha
  have hsi : Sorted lt is := Sorted.sublist (items_sublist_elemsAux is cs) hs
  exact not_lt_of_countLt_le ho is a i is[i] hsi hi1 (List.getElem?_eq_getElem hi2)

omit hok hs in
/-- Nothing at or above an entry `x` that is not below `stop` is in an ascending range. -/
theorem asc_nil_above (ks ku : Option K) (b : K) (hb : ku = some b) (x : V × K)
    (hx : ¬ lt x.2 b) (M : List (V × K)) (hM : ∀ e ∈ M, ¬ lt e.2 x.2) :
    ascRange lt M ks ku = [] := by
  apply ascRange_nil_of
  intro e he hin
  have heb := hin.2 b hb
  rcases ho.total e.2 x.2 with h1 | h1 | h1
  · exact hM e he h1
  · exact hx (h1 ▸ heb)
  · exact hx (ho.trans _ _ _ h1 heb)

omit ho in
/-- The range of a node, split at child `j`. -/
theorem asc_decomp (ks ku : Option K) (j : Nat) (hj : j ≤ is.length) :
    ascRange lt (Tree.elemsAux is cs) ks ku =
      ascRange lt (preElems is cs j) ks ku ++ ascRange lt (chElems cs j) ks ku ++
        ascRange lt (sufElems is cs j) ks ku := by
  rw [elems_decomp j is cs hok hj, ascRange_append, ascRange_append]

omit ho hs in
theorem asc_pre_succ (ks ku : Option K) (j : Nat) (hj : j < is.length) :
    ascRange lt (preElems is cs (j + 1)) ks ku =
      ascRange lt (preElems is cs j) ks ku ++ ascRange lt (chElems cs j) ks ku ++
        (if ascIn lt ks ku is[j].2 then [is[j]] else []) := by
  rw [preElems_succ is cs j hok hj, ascRange_append, ascRange_append]
  by_cases hin : ascIn lt ks ku is[j].2 <;> simp [ascRange, hin]

/-! #### Descending -/

/-- Where a descending iteration starts in a node: after the last item not above
`start` (as the number of items up to it). -/
def descStart (lt : K → K → Prop) (is : List (V × K)) : Option K → Nat
  | some a => if ∃ e, is[countLt lt is a]? = some e ∧ e.2 = a then countLt lt is a + 1
    else countLt lt is a
  | none => is.length

omit ho hok hs in
theorem descStart_le (ks : Option K) : descStart lt is ks ≤ is.length := by
  cases ks with
  | none => simp [descStart]
  | some a =>
    simp only [descStart]
    split
    · rename_i h
      obtain ⟨e, he, _⟩ := h
      have := (List.getElem?_eq_some_iff.1 he).1
      omega
    · exact countLt_le is a

theorem desc_suf_start (ks ku : Option K) :
    descRange lt (sufElems is cs (descStart lt is ks)) ks ku = [] := by
  cases ks with
  | none => simp [descStart, sufElems_length, descRange]
  | some a =>
    apply descRange_nil_of
    intro e he hin
    have hea := hin.1 a rfl
    have hsi : Sorted lt is := Sorted.sublist (items_sublist_elemsAux is cs) hs
    simp only [descStart] at he
    split at he
    · rename_i hf
      obtain ⟨x, hx, hxa⟩ := hf
      have hjl := (List.getElem?_eq_some_iff.1 hx).1
      have hxe : is[countLt lt is a] = x := (List.getElem?_eq_some_iff.1 hx).2
      have := item_lt ho hok hs _ hjl e (by simp [he])
      rw [hxe, hxa] at this
      exact hea this
    · rename_i hnf
      by_cases hjl : countLt lt is a < is.length
      · have hx := not_lt_of_countLt_le ho is a _ is[countLt lt is a] hsi (Nat.le_refl _)
          (List.getElem?_eq_getElem hjl)
        have hne : is[countLt lt is a].2 ≠ a := fun h' =>
          hnf ⟨_, List.getElem?_eq_getElem hjl, h'⟩
        have hax : lt a is[countLt lt is a].2 := by
          rcases ho.total is[countLt lt is a].2 a with h1 | h1 | h1
          · exact absurd h1 hx
          · exact absurd h1 hne
          · exact h1
        rw [sufElems_succ is cs _ hok hjl] at he
        rcases List.mem_cons.1 he with rfl | he
        · exact hea hax
        · exact hea (ho.trans _ _ _ hax (item_lt ho hok hs _ hjl e he))
      · have : countLt lt is a = is.length := by
          have := countLt_le (lt := lt) is a; omega
        rw [this, sufElems_length] at he; simp at he

omit hok in
theorem item_le_descStart (a : K) (i : Nat) (hi : i < descStart lt is (some a))
    (hil : i < is.length) : ¬ lt a is[i].2 := by
  have hsi : Sorted lt is := Sorted.sublist (items_sublist_elemsAux is cs) hs
  simp only [descStart] at hi
  split at hi
  · rename_i hf
    obtain ⟨x, hx, hxa⟩ := hf
    have hjl := (List.getElem?_eq_some_iff.1 hx).1
    have hxe : is[countLt lt is a]'hjl = x := (List.getElem?_eq_some_iff.1 hx).2
    by_cases hic : i = countLt lt is a
    · subst hic; rw [hxe, hxa]; exact ho.irrefl a
    · have := lt_of_lt_countLt (lt := lt) is a i is[i] (by omega) (List.getElem?_eq_getElem hil)
      intro h'; exact ho.irrefl _ (ho.trans _ _ _ this h')
  · have := lt_of_lt_countLt (lt := lt) is a i is[i] hi (List.getElem?_eq_getElem hil)
    intro h'; exact ho.irrefl _ (ho.trans _ _ _ this h')

omit hok in
theorem descIn_item (ks ku : Option K) (i : Nat) (hi1 : i < descStart lt is ks)
    (hi2 : i < is.length) (hstop : ∀ b, ku = some b → lt b is[i].2) :
    descIn lt ks ku is[i].2 := by
  refine ⟨?_, hstop⟩
  intro a ha
  subst ha
  exact item_le_descStart ho hs a i hi1 hi2

omit hok hs in
/-- Nothing at or below an entry `x` that is not above `stop` is in a descending range. -/
theorem desc_nil_below (ks ku : Option K) (b : K) (hb : ku = some b) (x : V × K)
    (hx : ¬ lt b x.2) (M : List (V × K)) (hM : ∀ e ∈ M, ¬ lt x.2 e.2) :
    descRange lt M ks ku = [] := by
  apply descRange_nil_of
  intro e he hin
  have heb := hin.2 b hb
  rcases ho.total e.2 x.2 with h1 | h1 | h1
  · exact hx (ho.trans _ _ _ heb h1)
  · exact hx (h1 ▸ heb)
  · exact hM e he h1

omit ho in
theorem desc_decomp (ks ku : Option K) (j : Nat) (hj : j ≤ is.length) :
    descRange lt (Tree.elemsAux is cs) ks ku =
      descRange lt (sufElems is cs j) ks ku ++ descRange lt (chElems cs j) ks ku ++
        descRange lt (preElems is cs j) ks ku := by
  rw [elems_decomp j is cs hok hj, descRange_append, descRange_append]
  simp

omit ho hs in
theorem desc_suf_pred (ks ku : Option K) (j : Nat) (hj : j < is.length) :
    descRange lt (sufElems is cs j) ks ku =
      descRange lt (sufElems is cs (j + 1)) ks ku ++ descRange lt (chElems cs (j + 1)) ks ku ++
        (if descIn lt ks ku is[j].2 then [is[j]] else []) := by
  rw [sufElems_succ is cs j hok hj, descRange_cons, descRange_append]

/-- Once a descending iteration has visited an entry (or was told so), everything still
ahead of it is below `start`. -/
theorem desc_hit_lt (a : K) (ku : Option K) (hit : Bool) (j : Nat) (hj : j ≤ is.length)
    (hhit : hit = true → ∀ e ∈ Tree.elemsAux is cs, lt e.2 a)
    (hh : (hit || !(descRange lt (sufElems is cs j) (some a) ku).isEmpty) = true) :
    ∀ e ∈ preElems is cs j ++ chElems cs j, lt e.2 a := by
  intro e he
  cases hit with
  | true =>
    apply hhit rfl
    rw [elems_decomp j is cs hok hj]
    simp only [List.mem_append] at he ⊢
    exact Or.inl he
  | false =>
    simp only [Bool.false_or, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.isEmpty_eq_false_iff] at hh
    obtain ⟨e', he'⟩ := List.exists_mem_of_ne_nil _ hh
    simp only [descRange, List.mem_reverse, List.mem_filter, decide_eq_true_eq] at he'
    have hlt := lt_pre_ch_suf ho hok hs j hj e he e' he'.1
    have hle := he'.2.1 a rfl
    rcases ho.total e'.2 a with h1 | h1 | h1
    · exact ho.trans _ _ _ hlt h1
    · exact h1 ▸ hlt
    · exact absurd h1 hle

end iter

end pure

/-! ## Read access to nodes -/

section sep
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {K : Type}
variable (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc)

theorem read_ownNodes_of_frozenList (dq : DFrac) :
    ∀ (ps : List Loc) (ts : List (Tree (V × K))),
      frozenList o c f less ps ts ⊢ ownNodes o c f less dq ps ts
  | [], [] => by rw [frozenList_nil, ownNodes_nil]
  | p :: ps, t :: ts => by
    rw [frozenList_cons, ownNodes_cons]
    iintro ⟨H1, H2⟩
    isplitl [H1]
    · iapply ownNode_of_frozen; iexact H1
    · iapply read_ownNodes_of_frozenList dq ps ts $$ H2
  | [], _ :: _ => by rw [frozenList]; iintro %h; exact h.elim
  | _ :: _, [] => by rw [frozenList]; iintro %h; exact h.elim

/-- Read access to a node, owned or frozen: its fields (at some fraction), the context
it names, its item and child slices, and its children; all given back to restore the
node. -/
theorem ownNode_read (dq : DFrac) (n : Loc) (is : List (V × K)) (cs : List (Tree (V × K))) :
    isCow o c f less ∗ ownNode o c f less dq n (.node is cs) ⊢
      ∃ (dq' : DFrac) (isl csl : GoSlice) (cow : Loc) (ps : List Loc),
        nodeFields (V := V) n dq' isl csl cow ∗ isCow o cow f less ∗
        isl ↦*{dq'} is.map Prod.fst ∗ csl ↦*{dq'} ps ∗ ownNodes o c f less dq ps cs ∗
        (nodeFields (V := V) n dq' isl csl cow ∗ isl ↦*{dq'} is.map Prod.fst ∗
          csl ↦*{dq'} ps ∗ ownNodes o c f less dq ps cs -∗
          ownNode o c f less dq n (.node is cs)) := by
  iintro ⟨#Hcow, Hn⟩
  icases (ownNode_unfold o c f less dq n _).1 $$ Hn with (Hown | #Hfr)
  · unfold ownedNode nodeShallow
    simp only [Tree.items_node, Tree.children_node]
    icases Hown with ⟨%ps, ⟨%isl, %csl, Hnf, Hisl, Hiscap, Hcsl, Hcscap⟩, Hch⟩
    iexists dq, isl, csl, c, ps
    iframe Hnf Hcow Hisl Hcsl Hch
    iintro ⟨Hnf, Hisl, Hcsl, Hch⟩
    iapply ownNode_of_owned
    unfold ownedNode nodeShallow
    simp only [Tree.items_node, Tree.children_node]
    iexists ps
    iframe Hch
    iexists isl, csl
    iframe
  · rw [frozen_node]
    icases Hfr with ⟨%isl, %csl, %cow, %ps, #Hnf, %Hne, #Hcow', #Hisl, #Hcsl, #Hfl⟩
    iexists DFrac.discard, isl, csl, cow, ps
    iframe Hnf Hcow' Hisl Hcsl
    isplitl []
    · iapply read_ownNodes_of_frozenList $$ Hfl
    iintro _
    iapply ownNode_of_frozen
    rw [frozen_node]
    iexists isl, csl, cow, ps
    iframe Hnf Hcow' Hisl Hcsl Hfl
    ipureintro; exact Hne

/-- The `less` field of a context (for `n.cow.less`). -/
theorem isCow_less (cw : Loc) :
    isCow o cw f less ⊢
      structFieldRef (copyOnWriteContext V) go!"less" cw ↦□ less := by
  unfold isCow
  iintro ⟨Hc, _, _⟩
  iStructNamed Hc
  iexact less

theorem isCow_isLess (cw : Loc) : isCow o cw f less ⊢ isLess o less := by
  unfold isCow
  iintro ⟨_, _, H⟩
  iexact H

theorem allItems_mono {l1 l2 : List (V × K)} (h : ∀ e ∈ l1, e ∈ l2) :
    allItems o l2 ⊢ allItems o l1 := by
  unfold allItems
  iintro #H
  imodintro
  iintro %e %he
  iapply H
  ipureintro; exact h e he

theorem allItems_elem {l : List (V × K)} {e : V × K} (h : e ∈ l) :
    allItems o l ⊢ o.item e.1 e.2 := by
  unfold allItems
  iintro #H
  iapply H
  ipureintro; exact h

/-- Read access to a node, owned or frozen, without its context. -/
theorem ownNode_peek (dq : DFrac) (n : Loc) (is : List (V × K)) (cs : List (Tree (V × K))) :
    ownNode o c f less dq n (.node is cs) ⊢
      ∃ (dq' : DFrac) (isl csl : GoSlice) (cow : Loc) (ps : List Loc),
        nodeFields (V := V) n dq' isl csl cow ∗
        isl ↦*{dq'} is.map Prod.fst ∗ csl ↦*{dq'} ps ∗ ownNodes o c f less dq ps cs ∗
        (nodeFields (V := V) n dq' isl csl cow ∗ isl ↦*{dq'} is.map Prod.fst ∗
          csl ↦*{dq'} ps ∗ ownNodes o c f less dq ps cs -∗
          ownNode o c f less dq n (.node is cs)) := by
  iintro Hn
  icases (ownNode_unfold o c f less dq n _).1 $$ Hn with (Hown | #Hfr)
  · unfold ownedNode nodeShallow
    simp only [Tree.items_node, Tree.children_node]
    icases Hown with ⟨%ps, ⟨%isl, %csl, Hnf, Hisl, Hiscap, Hcsl, Hcscap⟩, Hch⟩
    iexists dq, isl, csl, c, ps
    iframe Hnf Hisl Hcsl Hch
    iintro ⟨Hnf, Hisl, Hcsl, Hch⟩
    iapply ownNode_of_owned
    unfold ownedNode nodeShallow
    simp only [Tree.items_node, Tree.children_node]
    iexists ps
    iframe Hch
    iexists isl, csl
    iframe
  · rw [frozen_node]
    icases Hfr with ⟨%isl, %csl, %cow, %ps, #Hnf, %Hne, #Hcow', #Hisl, #Hcsl, #Hfl⟩
    iexists DFrac.discard, isl, csl, cow, ps
    iframe Hnf Hisl Hcsl
    isplitl []
    · iapply read_ownNodes_of_frozenList $$ Hfl
    iintro _
    iapply ownNode_of_frozen
    rw [frozen_node]
    iexists isl, csl, cow, ps
    iframe Hnf Hcow' Hisl Hcsl Hfl
    ipureintro; exact Hne

theorem optKey_valid (oi : optionalItem V) (ks : Option K) :
    optKey o oi ks ⊢ ⌜(oi.valid' = true → ∃ a, ks = some a) ∧ (oi.valid' = false → ks = none)⌝ := by
  unfold optKey
  cases hv : oi.valid'
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro %h; ipureintro; simp [h]
  · simp only [↓reduceIte]
    iintro ⟨%k, %hk, _⟩; ipureintro; simp [hk]

theorem optKey_some (oi : optionalItem V) (a : K) :
    optKey o oi (some a) ⊢ o.item oi.item' a := by
  unfold optKey
  cases hv : oi.valid'
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro %h; simp at h
  · simp only [↓reduceIte]
    iintro ⟨%k, %hk, H⟩
    cases hk
    iexact H

/-- What `node.iterate`'s postcondition gives the iteration methods (which start with
nothing visited). -/
theorem iterDone_of_iterate (r seg : List (V × K)) (hseg : seg = r)
    (I : List (V × K) → Bool → IProp GF) (ok : Bool) (W X : Prop) :
    iprop((⌜ok = true ∧ W⌝ ∗ I ([] ++ seg) false) ∨
      (⌜ok = false⌝ ∗ ((∃ pre, ⌜[] <+: pre ∧ pre <+: [] ++ seg⌝ ∗ I pre true) ∨
        (I ([] ++ seg) false ∗ ⌜X⌝)))) ⊢ iterDone r I := by
  subst hseg
  unfold iterDone
  simp only [List.nil_append]
  iintro (⟨_, HI⟩ | ⟨_, (⟨%pre, %Hpre, HI⟩ | ⟨HI, _⟩)⟩)
  · iexists seg, false; iframe; ipureintro; exact ⟨List.prefix_refl _, fun _ => rfl⟩
  · iexists pre, true; iframe; ipureintro; exact ⟨Hpre.2, fun h => absurd h (by simp)⟩
  · iexists seg, false; iframe; ipureintro; exact ⟨List.prefix_refl _, fun _ => rfl⟩

/-- An empty iteration is done. -/
theorem iterDone_nil (I : List (V × K) → Bool → IProp GF) : I [] false ⊢ iterDone [] I := by
  unfold iterDone
  iintro HI
  iexists [], false; iframe; ipureintro; exact ⟨List.prefix_refl _, fun _ => rfl⟩

theorem optKey_empty : ⊢ optKey o (optionalItem.mk (zero_val V) false) (none : Option K) := by
  unfold optKey
  simp only [Bool.false_eq_true, ↓reduceIte]
  ipureintro; trivial

theorem optKey_optional (v : V) (k : K) :
    o.item v k ⊢ optKey o (optionalItem.mk v true) (some k) := by
  unfold optKey
  simp only [↓reduceIte]
  iintro #H
  iexists k
  isplitr
  · ipureintro; rfl
  iexact H

theorem ownNode_not_null (dq : DFrac) (n : Loc) (t : Tree (V × K)) :
    ownNode o c f less dq n t ⊢ ⌜n ≠ null⌝ := by
  obtain ⟨is, cs⟩ := t
  iintro Hn
  icases (ownNode_unfold o c f less dq n _).1 $$ Hn with (Hown | Hfr)
  · unfold ownedNode nodeShallow nodeFields
    icases Hown with ⟨%ps, ⟨%isl, %csl, ⟨%Hnn, _⟩, _⟩, _⟩
    ipureintro; exact Hnn
  · rw [frozen_node]
    unfold nodeFields
    icases Hfr with ⟨%isl, %csl, %cow, %ps, ⟨%Hnn, _⟩, _⟩
    ipureintro; exact Hnn

/-- The fields of a tree's header, and back. -/
theorem btree_fields (t : Loc) (tv : BTree V) (dq : DFrac) :
    (t ↦{dq} tv : IProp GF) ⊢
      t.[BTree V, go!"degree"] ↦{dq} tv.degree' ∗ t.[BTree V, go!"length"] ↦{dq} tv.length' ∗
      t.[BTree V, go!"root"] ↦{dq} tv.root' ∗ t.[BTree V, go!"cow"] ↦{dq} tv.cow' ∗
      (t.[BTree V, go!"degree"] ↦{dq} tv.degree' ∗ t.[BTree V, go!"length"] ↦{dq} tv.length' ∗
        t.[BTree V, go!"root"] ↦{dq} tv.root' ∗ t.[BTree V, go!"cow"] ↦{dq} tv.cow' -∗
        t ↦{dq} tv) := by
  iintro Ht
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  iframe degree length root cow
  iintro ⟨degree, length, root, cow⟩
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end sep

end btree
end EtcdGrove
end Perennial
