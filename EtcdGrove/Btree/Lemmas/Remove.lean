/-
Lemmas for removal (`node.remove`, `node.growChildAndRemove`, `BTreeG.deleteItem`): the
in-order contents of a node split at a child, sortedness around a position, `countLt`,
`removeOp` on the parts of a sorted list, and the shape after removing from a leaf,
descending, replacing a found item by its predecessor, stealing from a sibling and merging.
-/
import EtcdGrove.Btree.NodeLemmas

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

/-! The removal lemmas live in their own namespace (`open RemoveLemmas`). -/
namespace RemoveLemmas

open Tree

open Classical

/-! ## In-order contents -/

variable {E : Type}

/-- What follows child `b` in `elemsAux is (b :: cs)`. -/
def restAux : List E → List (Tree E) → List E
  | [], cs => elemsAux [] cs
  | i :: is, cs => i :: elemsAux is cs

@[simp] theorem restAux_nil (cs : List (Tree E)) : restAux [] cs = elemsAux [] cs := rfl
@[simp] theorem restAux_cons (i : E) (is : List E) (cs : List (Tree E)) :
    restAux (i :: is) cs = i :: elemsAux is cs := rfl

theorem elemsAux_cons_child (is : List E) (b : Tree E) (cs : List (Tree E)) :
    elemsAux is (b :: cs) = elems b ++ restAux is cs := by
  cases is <;> simp

theorem elemsAux_append : ∀ (is1 is2 : List E) (cs1 cs2 : List (Tree E)),
    is1.length = cs1.length →
    elemsAux (is1 ++ is2) (cs1 ++ cs2) = elemsAux is1 cs1 ++ elemsAux is2 cs2
  | [], is2, [], cs2, _ => by simp
  | i :: is1, is2, c :: cs1, cs2, h => by
    simp only [List.cons_append, elemsAux_cons_cons, List.append_assoc]
    rw [elemsAux_append is1 is2 cs1 cs2 (by simpa using h)]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h

theorem elemsAux_append_item : ∀ (A B : List E) (x : E) (Ac Bc : List (Tree E)),
    Ac.length = A.length + 1 →
    elemsAux (A ++ x :: B) (Ac ++ Bc) = elemsAux A Ac ++ x :: elemsAux B Bc
  | [], B, x, [y], Bc, _ => by simp
  | a :: A, B, x, c :: Ac, Bc, h => by
    simp only [List.cons_append, elemsAux_cons_cons, List.append_assoc]
    rw [elemsAux_append_item A B x Ac Bc (by simpa using h)]
  | [], _, _, [], _, h => by simp at h
  | [], _, _, _ :: _ :: _, _, h => by simp at h
  | _ :: _, _, _, [], _, h => by simp at h

/-- Splitting at child `a`. -/
theorem elemsAux_split1 (P Q : List E) (Pc Qc : List (Tree E)) (a : Tree E)
    (h : P.length = Pc.length) :
    elemsAux (P ++ Q) (Pc ++ a :: Qc) = elemsAux P Pc ++ (elems a ++ restAux Q Qc) := by
  rw [elemsAux_append _ _ _ _ h, elemsAux_cons_child]

/-- Splitting at the window child `a`, item `x`, child `b`. -/
theorem elemsAux_split2 (P Q : List E) (Pc Qc : List (Tree E)) (a b : Tree E) (x : E)
    (h : P.length = Pc.length) :
    elemsAux (P ++ x :: Q) (Pc ++ a :: b :: Qc) =
      elemsAux P Pc ++ (elems a ++ x :: (elems b ++ restAux Q Qc)) := by
  rw [elemsAux_split1 _ _ _ _ _ h, restAux_cons, elemsAux_cons_child]

/-- The items of a node are a sublist of its contents. -/
theorem items_sublist_elemsAux : ∀ (is : List E) (cs : List (Tree E)), is.Sublist (elemsAux is cs)
  | [], _ => List.nil_sublist _
  | i :: is, [] => by simp
  | i :: is, c :: cs => by
    rw [elemsAux_cons_cons]
    exact (List.Sublist.cons_cons i (items_sublist_elemsAux is cs)).trans
      (List.sublist_append_right _ _)

theorem items_sublist_elems (t : Tree E) : t.items.Sublist t.elems := by
  cases t with
  | node is cs => simpa using items_sublist_elemsAux is cs

theorem elems_ne_nil (t : Tree E) (h : 1 ≤ t.items.length) : t.elems ≠ [] := by
  intro he
  have := (items_sublist_elems t).length_le
  rw [he, List.length_nil] at this; omega



/-! ## Splitting a node's contents at an index -/

variable {E : Type}

/-- The contents before child `j`. -/
def pre (is : List E) (cs : List (Tree E)) (j : Nat) : List E :=
  elemsAux (is.take j) (cs.take j)

/-- The contents after child `j`. -/
def post (is : List E) (cs : List (Tree E)) (j : Nat) : List E :=
  restAux (is.drop j) (cs.drop (j + 1))

theorem split_at (is : List E) (cs : List (Tree E)) (j : Nat) (hj : j ≤ is.length)
    (hc : j < cs.length) :
    elemsAux is cs = pre is cs j ++ elems cs[j] ++ post is cs j := by
  conv => lhs; rw [← List.take_append_drop j is, ← List.take_append_drop j cs,
    List.drop_eq_getElem_cons hc]
  rw [elemsAux_split1 _ _ _ _ _ (by simp; omega), List.append_assoc]
  rfl

theorem pre_set (is : List E) (cs : List (Tree E)) (j : Nat) (b : Tree E) :
    pre is (cs.set j b) j = pre is cs j := by
  unfold pre; rw [List.take_set_of_le (Nat.le_refl _)]

theorem post_set (is : List E) (cs : List (Tree E)) (j : Nat) (b : Tree E) :
    post is (cs.set j b) j = post is cs j := by
  unfold post; rw [List.drop_set_of_lt (Nat.lt_succ_self _)]

theorem split_set (is : List E) (cs : List (Tree E)) (j : Nat) (b : Tree E)
    (hj : j ≤ is.length) (hc : j < cs.length) :
    elemsAux is (cs.set j b) = pre is cs j ++ elems b ++ post is cs j := by
  rw [split_at is (cs.set j b) j hj (by simpa using hc), pre_set, post_set]
  simp

theorem post_of_lt (is : List E) (cs : List (Tree E)) (j : Nat) (hj : j < is.length) :
    post is cs j = is[j] :: elemsAux (is.drop (j + 1)) (cs.drop (j + 1)) := by
  unfold post; rw [List.drop_eq_getElem_cons hj]; rfl

theorem post_of_eq (is : List E) (cs : List (Tree E)) (j : Nat) (hj : j = is.length)
    (hc : cs.length = is.length + 1) : post is cs j = [] := by
  unfold post; subst hj
  rw [List.drop_of_length_le (Nat.le_refl _), List.drop_of_length_le (by omega)]
  simp

theorem pre_zero (is : List E) (cs : List (Tree E)) : pre is cs 0 = [] := by
  simp [pre]

theorem pre_succ (is : List E) (cs : List (Tree E)) (j : Nat) (hj : j < is.length)
    (hc : j < cs.length) :
    pre is cs (j + 1) = pre is cs j ++ (elems cs[j] ++ [is[j]]) := by
  unfold pre
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem hc]
  simp only [Option.toList_some]
  rw [elemsAux_append _ _ _ _ (by simp; omega)]
  simp

/-- Splitting at item `j` (with the child `j` before it and `j + 1` after it). -/
theorem split_item (is : List E) (cs : List (Tree E)) (j : Nat) (hj : j < is.length)
    (hc : cs.length = is.length + 1) :
    elemsAux is cs = (pre is cs j ++ elems (cs[j]'(by omega))) ++
      is[j] :: elemsAux (is.drop (j + 1)) (cs.drop (j + 1)) := by
  rw [split_at is cs j (by omega) (by omega), post_of_lt is cs j hj]


/-! ## Sorted lists -/

section sorted
variable {V K : Type} {lt : K → K → Prop}

theorem sorted_sublist {l1 l2 : List (V × K)} (h : l1.Sublist l2) (hs : Sorted lt l2) :
    Sorted lt l1 := hs.sublist h

theorem sorted_append {A B : List (V × K)} :
    Sorted lt (A ++ B) ↔ Sorted lt A ∧ Sorted lt B ∧ ∀ a ∈ A, ∀ b ∈ B, lt a.2 b.2 := by
  unfold Sorted; exact List.pairwise_append

theorem sorted_cons {x : V × K} {B : List (V × K)} :
    Sorted lt (x :: B) ↔ (∀ b ∈ B, lt x.2 b.2) ∧ Sorted lt B := by
  unfold Sorted; exact List.pairwise_cons

/-- Around an entry of a sorted list. -/
theorem sorted_mid {A B : List (V × K)} {x : V × K} (hs : Sorted lt (A ++ x :: B)) :
    (∀ a ∈ A, lt a.2 x.2) ∧ (∀ b ∈ B, lt x.2 b.2) := by
  rw [sorted_append, sorted_cons] at hs
  exact ⟨fun a ha => hs.2.2 a ha x (by simp), hs.2.1.1⟩

theorem not_lt_of_lt {o : StrictOrder lt} {a b : K} (h : lt a b) : ¬ lt b a :=
  fun h' => o.irrefl _ (o.trans _ _ _ h h')

theorem ne_of_lt' {o : StrictOrder lt} {a b : K} (h : lt a b) : a ≠ b := by
  rintro rfl; exact o.irrefl _ h

end sorted

/-! ## `countLt` -/

section count
variable {V K : Type} {lt : K → K → Prop}

theorem countLt_cons (x : V × K) (xs : List (V × K)) (k : K) :
    countLt lt (x :: xs) k = if lt x.2 k then countLt lt xs k + 1 else 0 := by
  unfold countLt
  rw [List.takeWhile_cons]
  by_cases h : lt x.2 k <;> simp [h]

theorem countLt_eq_iff : ∀ (l : List (V × K)) (k : K) (j : Nat),
    countLt lt l k = j ↔ j ≤ l.length ∧ (∀ m (_ : m < j) (h' : m < l.length), lt (l[m]).2 k) ∧
      (∀ h : j < l.length, ¬ lt (l[j]).2 k)
  | [], k, j => by
    simp [countLt]
    constructor
    · intro h; omega
    · intro h; omega
  | x :: xs, k, j => by
    rw [countLt_cons]
    by_cases hx : lt x.2 k
    · simp only [hx, ite_true]
      cases j with
      | zero =>
        simp only [Nat.add_one_ne_zero, false_iff, not_and, List.length_cons]
        intro _ _ h; exact h (by simp) hx
      | succ j =>
        rw [Nat.add_right_cancel_iff, countLt_eq_iff xs k j]
        simp only [List.length_cons, Nat.add_le_add_iff_right, Nat.add_lt_add_iff_right,
          List.getElem_cons_succ]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨h1, ?_, h3⟩
          intro m hm hm'
          cases m with
          | zero => simpa using hx
          | succ m =>
            have := h2 m (by omega) (by simpa using hm')
            simp only [List.getElem_cons_succ]; exact this
        · rintro ⟨h1, h2, h3⟩
          refine ⟨h1, ?_, h3⟩
          intro m hm hm'
          have := h2 (m + 1) (by omega) (by simpa using hm')
          simp only [List.getElem_cons_succ] at this; exact this
    · simp only [hx, ite_false]
      constructor
      · rintro rfl; simp [hx]
      · rintro ⟨_, h2, h3⟩
        cases j with
        | zero => rfl
        | succ j =>
          have := h2 0 (by omega) (by simp)
          simp only [List.getElem_cons_zero] at this; exact absurd this hx

theorem countLt_le (l : List (V × K)) (k : K) : countLt lt l k ≤ l.length :=
  ((countLt_eq_iff l k _).1 rfl).1

end count

/-! ## `removeOp` on the parts of a sorted list -/

section removeOp
variable {V K : Type} {lt : K → K → Prop}

theorem delete_append (A B : List (V × K)) (k : K) :
    delete (A ++ B) k = delete A k ++ delete B k := by
  simp only [delete, List.filter_append]

theorem delete_of_ne (A : List (V × K)) (k : K) (h : ∀ e ∈ A, e.2 ≠ k) : delete A k = A := by
  unfold delete; rw [List.filter_eq_self]; intro e he; simpa using h e he

theorem lookup_append (A B : List (V × K)) (k : K) :
    lookup (A ++ B) k = (lookup A k).or (lookup B k) := by
  unfold lookup; rw [List.find?_append]; cases A.find? _ <;> simp

theorem lookup_of_ne (A : List (V × K)) (k : K) (h : ∀ e ∈ A, e.2 ≠ k) : lookup A k = none := by
  unfold lookup; rw [Option.map_eq_none_iff, List.find?_eq_none]; intro e he; simpa using h e he

@[simp] theorem lookup_cons_self (x : V × K) (B : List (V × K)) :
    lookup (x :: B) x.2 = some x.1 := by
  simp [lookup]

/-- Removing from the middle part `M` of `L ++ M ++ R`, when the target is in `M`'s range. -/
def InMid (tgt : Target K) (L M R : List (V × K)) : Prop :=
  match tgt with
  | .key k => (∀ e ∈ L, e.2 ≠ k) ∧ (∀ e ∈ R, e.2 ≠ k)
  | .min => L = [] ∧ M ≠ []
  | .max => R = [] ∧ M ≠ []

theorem removeOp_mid (tgt : Target K) (L M R : List (V × K)) (h : InMid tgt L M R) :
    removeOp tgt (L ++ M ++ R) = (L ++ (removeOp tgt M).1 ++ R, (removeOp tgt M).2) := by
  cases tgt with
  | key k =>
    obtain ⟨hL, hR⟩ := h
    simp only [removeOp, delete_append, delete_of_ne L k hL, delete_of_ne R k hR,
      lookup_append, lookup_of_ne L k hL, lookup_of_ne R k hR, Option.none_or]
    cases lookup M k <;> rfl
  | min =>
    obtain ⟨rfl, hM⟩ := h
    obtain ⟨x, M', rfl⟩ := List.exists_cons_of_ne_nil hM
    simp [removeOp]
  | max =>
    obtain ⟨rfl, hM⟩ := h
    simp only [removeOp, List.append_nil]
    rcases List.eq_nil_or_concat M with h0 | ⟨M', x, rfl⟩
    · exact absurd h0 hM
    · simp only [List.concat_eq_append]; rw [← List.append_assoc]; simp

end removeOp

/-! ## Keys around a position of an internal node -/

section keys
variable {V K : Type} {lt : K → K → Prop}


theorem before_item (is : List (V × K)) (cs : List (Tree (V × K))) (j : Nat)
    (hj : j < is.length) (hc : cs.length = is.length + 1) (hs : Sorted lt (elemsAux is cs)) :
    ∀ e ∈ pre is cs j ++ elems (cs[j]'(by omega)), lt e.2 (is[j]).2 := by
  rw [split_item is cs j hj hc] at hs
  exact (sorted_mid hs).1

theorem after_item (is : List (V × K)) (cs : List (Tree (V × K))) (j : Nat)
    (hj : j < is.length) (hc : cs.length = is.length + 1) (hs : Sorted lt (elemsAux is cs)) :
    ∀ e ∈ elemsAux (is.drop (j + 1)) (cs.drop (j + 1)), lt (is[j]).2 e.2 := by
  rw [split_item is cs j hj hc] at hs
  exact (sorted_mid hs).2

theorem pre_lt (ord : StrictOrder lt) (is : List (V × K)) (cs : List (Tree (V × K))) (j : Nat)
    (k : K) (hj : j ≤ is.length) (hc : cs.length = is.length + 1)
    (hs : Sorted lt (elemsAux is cs))
    (hlt : ∀ m (_ : m < j) (h' : m < is.length), lt (is[m]).2 k) :
    ∀ e ∈ pre is cs j, lt e.2 k := by
  cases j with
  | zero => simp [pre_zero]
  | succ j =>
    have hj' : j < is.length := by omega
    have hx := hlt j (by omega) hj'
    rw [pre_succ is cs j hj' (by omega)]
    intro e he
    have hb := before_item is cs j hj' hc hs
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | he | he
    · exact ord.trans _ _ _ (hb e (List.mem_append_left _ he)) hx
    · exact ord.trans _ _ _ (hb e (List.mem_append_right _ he)) hx
    · subst he; exact hx

theorem gt_of_not_lt_ne (ord : StrictOrder lt) {a k : K} (h1 : ¬ lt a k) (h2 : a ≠ k) :
    lt k a := by
  rcases ord.total a k with h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · exact h

/-- The child the removal descends into holds the target's range. -/
theorem inMid_desc (ord : StrictOrder lt) (tgt : Target K) (is : List (V × K))
    (cs : List (Tree (V × K))) (j : Nat) (hc : cs.length = is.length + 1)
    (hs : Sorted lt (elemsAux is cs)) (hj : j = remIdx lt tgt is) (hjc : j < cs.length)
    (hne : elems (cs[j]'hjc) ≠ [])
    (hnf : ∀ k, tgt = .key k → ¬ ∃ e, is[j]? = some e ∧ e.2 = k) :
    InMid tgt (pre is cs j) (elems (cs[j]'hjc)) (post is cs j) := by
  cases tgt with
  | key k =>
    simp only [remIdx] at hj
    obtain ⟨hjl, hlt, hge⟩ := (countLt_eq_iff is k j).1 hj.symm
    refine ⟨fun e he => ne_of_lt' (o := ord) (pre_lt ord is cs j k hjl hc hs hlt e he), ?_⟩
    by_cases hjl' : j < is.length
    · rw [post_of_lt is cs j hjl']
      have hne' : (is[j]).2 ≠ k := fun h => hnf k rfl ⟨_, List.getElem?_eq_getElem hjl', h⟩
      have hgt := gt_of_not_lt_ne ord (hge hjl') hne'
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact hne'
      · exact (ne_of_lt' (o := ord)
          (ord.trans _ _ _ hgt (after_item is cs j hjl' hc hs e he))).symm
    · rw [post_of_eq is cs j (by omega) hc]; simp
  | min =>
    simp only [remIdx] at hj; subst hj
    exact ⟨pre_zero is cs, hne⟩
  | max =>
    simp only [remIdx] at hj
    exact ⟨post_of_eq is cs j hj hc, hne⟩

end keys

/-! ## Shapes -/

variable {E : Type}

theorem shape_succ (d h : Nat) (is : List E) (cs : List (Tree E)) :
    Shape d (h + 1) (.node is cs) ↔ cs.length = is.length + 1 ∧
      ∀ c ∈ cs, (d - 1 ≤ c.items.length ∧ c.items.length ≤ 2 * d - 1) ∧ Shape d h c := by
  rw [Shape]

theorem shape_zero (d : Nat) (is : List E) (cs : List (Tree E)) :
    Shape d 0 (.node is cs) ↔ cs = [] := by
  rw [Shape]

theorem shape_child {d h : Nat} {is : List E} {cs : List (Tree E)} {j : Nat} {c : Tree E}
    (hs : Shape d (h + 1) (.node is cs)) (hc : cs[j]? = some c) :
    (d - 1 ≤ c.items.length ∧ c.items.length ≤ 2 * d - 1) ∧ Shape d h c :=
  ((shape_succ d h is cs).1 hs).2 c (List.mem_of_getElem? hc)

theorem shape_set {d h : Nat} {is is' : List E} {cs : List (Tree E)} (j : Nat) {b : Tree E}
    (hs : Shape d (h + 1) (.node is cs)) (hl : is'.length = is.length)
    (hb : (d - 1 ≤ b.items.length ∧ b.items.length ≤ 2 * d - 1) ∧ Shape d h b) :
    Shape d (h + 1) (.node is' (cs.set j b)) := by
  rw [shape_succ] at hs ⊢
  refine ⟨by simp [hs.1, hl], fun c hc => ?_⟩
  rcases List.mem_or_eq_of_mem_set hc with hc | rfl
  · exact hs.2 c hc
  · exact hb


/-! ## The removal postcondition -/

section post
variable {V K : Type}

/-- The postcondition of `node.remove`. -/
def RemPost (lt : K → K → Prop) (d h : Nat) (tgt : Target K) (t t' : Tree (V × K)) (out : V)
    (found : Bool) (z : V) : Prop :=
  t'.Shape d h ∧ t'.elems = (removeOp tgt t.elems).1 ∧
    out = ((removeOp tgt t.elems).2).getD z ∧
    found = ((removeOp tgt t.elems).2).isSome ∧
    t'.items.length ≤ t.items.length ∧ t.items.length ≤ t'.items.length + 1 ∧
    (0 < h → (∃ c1, t.children[remIdx lt tgt t.items]? = some c1 ∧ d ≤ c1.items.length) →
      t'.items.length = t.items.length)


/-- Descending into child `j` (the target is not an item of this node). -/
theorem rem_desc {lt : K → K → Prop} (ord : StrictOrder lt) (d h : Nat) (tgt : Target K)
    (is : List (V × K)) (cs : List (Tree (V × K))) (j : Nat) (cj cj' : Tree (V × K))
    (out : V) (found : Bool) (z : V)
    (hs : Shape d (h + 1) (.node is cs)) (hsort : Sorted lt (elemsAux is cs))
    (hj : j = remIdx lt tgt is) (hcj : cs[j]? = some cj) (hd : d ≤ cj.items.length) (hd1 : 1 ≤ d)
    (hnf : ∀ k, tgt = .key k → ¬ ∃ e, is[j]? = some e ∧ e.2 = k)
    (hpost : RemPost lt d h tgt cj cj' out found z) :
    RemPost lt d (h + 1) tgt (.node is cs) (.node is (cs.set j cj')) out found z := by
  obtain ⟨hs', he', hout, hfound, hl1, hl2, -⟩ := hpost
  have hc := ((shape_succ d h is cs).1 hs).1
  have hjc : j < cs.length := (List.getElem?_eq_some_iff.1 hcj).1
  have hcj' : cs[j]'hjc = cj := (List.getElem?_eq_some_iff.1 hcj).2
  have hjl : j ≤ is.length := by omega
  have hne : elems (cs[j]'hjc) ≠ [] := by rw [hcj']; exact elems_ne_nil cj (by omega)
  have hmid := inMid_desc ord tgt is cs j hc hsort hj hjc hne hnf
  rw [hcj'] at hmid
  have hb := shape_child hs hcj
  have hsplit : (Tree.node is cs).elems = pre is cs j ++ elems cj ++ post is cs j := by
    rw [elems_node, split_at is cs j hjl hjc, hcj']
  unfold RemPost
  rw [hsplit, removeOp_mid tgt _ _ _ hmid]
  refine ⟨shape_set j hs rfl ⟨⟨by omega, by omega⟩, hs'⟩, ?_, hout, hfound, by simp, by simp,
    fun _ _ => rfl⟩
  rw [elems_node, split_set is cs j cj' hjl hjc, he']

theorem drop_set_self {A : Type} (l : List A) (j : Nat) (a : A) (hj : j < l.length) :
    (l.set j a).drop j = a :: l.drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hj), List.drop_set_of_lt (Nat.lt_succ_self _)]
  simp

/-- The item with the key is at `j` of this internal node: it is replaced by its
predecessor, the largest entry of child `j`. -/
theorem rem_pred {lt : K → K → Prop} (ord : StrictOrder lt) (d h : Nat) (k : K)
    (is : List (V × K)) (cs : List (Tree (V × K))) (j : Nat) (x : V × K) (cj cj' : Tree (V × K))
    (out' : V) (found' : Bool) (z : V)
    (hs : Shape d (h + 1) (.node is cs)) (hsort : Sorted lt (elemsAux is cs))
    (hx : is[j]? = some x) (hxk : x.2 = k) (hcj : cs[j]? = some cj) (hd : d ≤ cj.items.length)
    (hd1 : 1 ≤ d) (hpost : RemPost lt d h .max cj cj' out' found' z) :
    ∃ e : V × K, out' = e.1 ∧
      RemPost lt d (h + 1) (.key k) (.node is cs) (.node (is.set j e) (cs.set j cj')) x.1 true z := by
  obtain ⟨hs', he', hout, -, hl1, hl2, -⟩ := hpost
  have hc := ((shape_succ d h is cs).1 hs).1
  have hjl : j < is.length := (List.getElem?_eq_some_iff.1 hx).1
  have hxj : is[j] = x := (List.getElem?_eq_some_iff.1 hx).2
  have hjc : j < cs.length := (List.getElem?_eq_some_iff.1 hcj).1
  have hcj' : cs[j]'hjc = cj := (List.getElem?_eq_some_iff.1 hcj).2
  have hne : elems cj ≠ [] := elems_ne_nil cj (by omega)
  refine ⟨cj.elems.getLast hne, ?_, ?_⟩
  · rw [hout]; simp [removeOp, List.getLast?_eq_some_getLast hne]
  have hb := shape_child hs hcj
  have hbef := before_item is cs j hjl hc hsort
  have haft := after_item is cs j hjl hc hsort
  rw [hcj', hxj, hxk] at hbef; rw [hxj, hxk] at haft
  have hsplit := split_item is cs j hjl hc
  rw [hcj', hxj] at hsplit
  have hdel : delete (Tree.node is cs).elems k =
      pre is cs j ++ elems cj ++ elemsAux (is.drop (j + 1)) (cs.drop (j + 1)) := by
    rw [elems_node, hsplit, delete_append, delete_of_ne _ k (fun e he => ne_of_lt' (o := ord)
      (hbef e he))]
    rw [show x :: elemsAux (is.drop (j + 1)) (cs.drop (j + 1)) =
      [x] ++ elemsAux (is.drop (j + 1)) (cs.drop (j + 1)) from rfl, delete_append,
      delete_of_ne _ k (fun e he => (ne_of_lt' (o := ord) (haft e he)).symm)]
    simp [delete, hxk]
  have hlook : lookup (Tree.node is cs).elems k = some x.1 := by
    rw [elems_node, hsplit, lookup_append, lookup_of_ne _ k (fun e he => ne_of_lt' (o := ord)
      (hbef e he)), Option.none_or, ← hxk, lookup_cons_self]
  unfold RemPost
  simp only [removeOp, hdel, hlook, Option.getD_some, Option.isSome_some]
  refine ⟨shape_set j hs (by simp) ⟨⟨by omega, by omega⟩, hs'⟩, ?_, trivial, trivial, by simp, by simp,
    fun _ _ => by simp⟩
  rw [elems_node, split_set (is.set j _) cs j cj' (by simp; omega) hjc]
  rw [show pre (is.set j (cj.elems.getLast hne)) cs j = pre is cs j by
      unfold pre; rw [List.take_set_of_le (Nat.le_refl _)],
    show post (is.set j (cj.elems.getLast hne)) cs j =
      cj.elems.getLast hne :: elemsAux (is.drop (j + 1)) (cs.drop (j + 1)) by
      unfold post; rw [drop_set_self is j _ hjl]; rfl,
    he']
  simp only [removeOp]
  conv => rhs; rw [← List.dropLast_concat_getLast hne]
  simp

/-! ### Leaves -/

theorem rem_leaf_max {lt : K → K → Prop} (d : Nat) (is : List (V × K)) (z : V) (hne : is ≠ []) :
    RemPost lt d 0 .max (.node is []) (.node is.dropLast []) (is.getLast hne).1 true z := by
  unfold RemPost
  simp only [removeOp, elems_node, elemsAux_nil, List.getLast?_eq_some_getLast hne]
  refine ⟨by rw [shape_zero], by simp, by simp, by simp, by simp, ?_, fun h => absurd h (by omega)⟩
  simp only [items_node, List.length_dropLast]
  have : 0 < is.length := List.length_pos_iff.2 hne
  omega

theorem rem_leaf_min {lt : K → K → Prop} (d : Nat) (is : List (V × K)) (x : V × K) (z : V)
    (hx : is[0]? = some x) :
    RemPost lt d 0 .min (.node is []) (.node (is.drop 1) []) x.1 true z := by
  obtain ⟨y, is', rfl⟩ : ∃ y is', is = y :: is' := by
    cases is with
    | nil => simp at hx
    | cons y is' => exact ⟨y, is', rfl⟩
  simp at hx; subst hx
  unfold RemPost
  simp only [removeOp, elems_node, elemsAux_nil]
  refine ⟨by rw [shape_zero], by simp, by simp, by simp, by simp, by simp, fun h => absurd h (by omega)⟩

theorem rem_leaf_key_found {lt : K → K → Prop} (ord : StrictOrder lt) (d : Nat) (k : K)
    (is : List (V × K)) (j : Nat) (x : V × K) (z : V) (hsort : Sorted lt is)
    (hx : is[j]? = some x) (hxk : x.2 = k) :
    RemPost lt d 0 (.key k) (.node is []) (.node (is.take j ++ is.drop (j + 1)) []) x.1 true z := by
  have hjl : j < is.length := (List.getElem?_eq_some_iff.1 hx).1
  have hxj : is[j] = x := (List.getElem?_eq_some_iff.1 hx).2
  have hsplit : is = is.take j ++ x :: is.drop (j + 1) := by
    rw [← hxj, List.getElem_cons_drop, List.take_append_drop]
  have hm := sorted_mid (hsplit ▸ hsort)
  rw [hxk] at hm
  have hdel : delete is k = is.take j ++ is.drop (j + 1) := by
    conv => lhs; rw [hsplit]
    rw [delete_append, delete_of_ne _ k (fun e he => ne_of_lt' (o := ord) (hm.1 e he)),
      show x :: is.drop (j + 1) = [x] ++ is.drop (j + 1) from rfl, delete_append,
      delete_of_ne _ k (fun e he => (ne_of_lt' (o := ord) (hm.2 e he)).symm)]
    simp [delete, hxk]
  have hlook : lookup is k = some x.1 := by
    conv => lhs; rw [hsplit]
    rw [lookup_append, lookup_of_ne _ k (fun e he => ne_of_lt' (o := ord) (hm.1 e he)),
      Option.none_or, ← hxk, lookup_cons_self]
  unfold RemPost
  simp only [removeOp, elems_node, elemsAux_nil, hdel, hlook, Option.getD_some,
    Option.isSome_some]
  refine ⟨by rw [shape_zero], by simp, by simp, by simp, ?_, ?_, fun h => absurd h (by omega)⟩ <;>
    simp only [items_node, List.length_append, List.length_take, List.length_drop] <;> omega

theorem rem_leaf_key_notfound {lt : K → K → Prop} (ord : StrictOrder lt) (d : Nat) (k : K)
    (is : List (V × K)) (j : Nat) (z : V) (hsort : Sorted lt is) (hj : j = countLt lt is k)
    (hnf : ¬ ∃ e, is[j]? = some e ∧ e.2 = k) :
    RemPost lt d 0 (.key k) (.node is []) (.node is []) z false z := by
  obtain ⟨hjl, hlt, hge⟩ := (countLt_eq_iff is k j).1 hj.symm
  have hall : ∀ e ∈ is, e.2 ≠ k := by
    intro e he
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 he
    by_cases hmj : m < j
    · exact ne_of_lt' (o := ord) (hlt m hmj hm)
    · have hjl' : j < is.length := by omega
      have hne' : (is[j]).2 ≠ k := fun h => hnf ⟨_, List.getElem?_eq_getElem hjl', h⟩
      have hgt := gt_of_not_lt_ne ord (hge hjl') hne'
      by_cases hmj' : m = j
      · subst hmj'; exact hne'
      · have := List.pairwise_iff_getElem.1 hsort j m hjl' hm (by omega)
        exact (ne_of_lt' (o := ord) (ord.trans _ _ _ hgt this)).symm
  unfold RemPost
  simp only [removeOp, elems_node, elemsAux_nil, delete_of_ne is k hall, lookup_of_ne is k hall,
    Option.getD_none, Option.isSome_none]
  exact ⟨by rw [shape_zero], by simp, by simp, by simp, Nat.le_refl _, by omega, fun _ _ => trivial⟩

/-- `remove` called `growChildAndRemove` (the child it descends into has too few items). -/
theorem rem_grow {lt : K → K → Prop} (d h : Nat) (tgt : Target K) (t t' : Tree (V × K))
    (out : V) (found : Bool) (z : V) (ci : Tree (V × K))
    (hci : t.children[remIdx lt tgt t.items]? = some ci) (hcil : ci.items.length ≤ d - 1)
    (hd1 : 1 ≤ d)
    (hpost : t'.Shape d h ∧ t'.elems = (removeOp tgt t.elems).1 ∧
      out = ((removeOp tgt t.elems).2).getD z ∧ found = ((removeOp tgt t.elems).2).isSome ∧
      t'.items.length ≤ t.items.length ∧ t.items.length ≤ t'.items.length + 1) :
    RemPost lt d h tgt t t' out found z := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpost
  refine ⟨h1, h2, h3, h4, h5, h6, fun _ ⟨c1, hc1, hd⟩ => ?_⟩
  rw [hci] at hc1; cases hc1; omega

theorem remIdx_le (lt : K → K → Prop) (tgt : Target K) (is : List (V × K)) :
    remIdx lt tgt is ≤ is.length := by
  cases tgt <;> simp only [remIdx] <;> first | omega | exact countLt_le is _

theorem remIdx_nil (lt : K → K → Prop) (tgt : Target K) : remIdx lt tgt ([] : List (V × K)) = 0 := by
  cases tgt <;> simp [remIdx, countLt]

theorem child_elems_sublist (is : List (V × K)) (cs : List (Tree (V × K))) (j : Nat)
    (ch : Tree (V × K)) (hc : cs[j]? = some ch) (hj : j ≤ is.length) :
    ch.elems.Sublist (elemsAux is cs) := by
  have hjc : j < cs.length := (List.getElem?_eq_some_iff.1 hc).1
  have hcj : cs[j] = ch := (List.getElem?_eq_some_iff.1 hc).2
  rw [split_at is cs j hj hjc, hcj]
  exact (List.sublist_append_right _ _).trans (List.sublist_append_left _ _)

end post

/-! ## Growing a child: stealing and merging -/

theorem rm_split1 {A : Type} (l : List A) (j : Nat) (h : j < l.length) :
    ∃ P x Q, l = P ++ x :: Q ∧ P.length = j := by
  refine ⟨l.take j, l[j], l.drop (j + 1), ?_, by simp; omega⟩
  rw [List.getElem_cons_drop, List.take_append_drop]

theorem rm_split2 {A : Type} (l : List A) (j : Nat) (h : j + 1 < l.length) :
    ∃ P a b Q, l = P ++ a :: b :: Q ∧ P.length = j := by
  obtain ⟨P, a, Q, rfl, hP⟩ := rm_split1 l j (by omega)
  cases Q with
  | nil => simp at h; omega
  | cons b Q => exact ⟨P, a, b, Q, rfl, hP⟩

section mid
variable {A : Type}

@[simp] theorem set_mid0 (P Q : List A) (a b a' : A) :
    (P ++ a :: b :: Q).set P.length a' = P ++ a' :: b :: Q := by
  induction P <;> simp_all

@[simp] theorem set_mid1 (P Q : List A) (a b b' : A) :
    (P ++ a :: b :: Q).set (P.length + 1) b' = P ++ a :: b' :: Q := by
  induction P <;> simp_all

@[simp] theorem set_mid (P Q : List A) (a a' : A) :
    (P ++ a :: Q).set P.length a' = P ++ a' :: Q := by
  induction P <;> simp_all

theorem take_drop_mid (P Q : List A) (x : A) :
    (P ++ x :: Q).take P.length ++ (P ++ x :: Q).drop (P.length + 1) = P ++ Q := by
  induction P <;> simp_all

theorem take_drop_mid1 (P Q : List A) (a b : A) :
    (P ++ a :: b :: Q).take (P.length + 1) ++ (P ++ a :: b :: Q).drop (P.length + 1 + 1) =
      P ++ a :: Q := by
  have := take_drop_mid (P ++ [a]) Q b
  simpa using this

end mid

section grow
variable {V K : Type}

/-- What `growChildAndRemove` establishes before it calls `remove` again: the same
contents, a well-shaped node that `remove` accepts, and if it lost an item (a merge),
`remove` descends into a child that need not grow. -/
def GrowMid (lt : K → K → Prop) (d h : Nat) (tgt : Target K) (t t'' : Tree (V × K)) : Prop :=
  t''.Shape d h ∧ t''.elems = t.elems ∧ t''.items.length ≤ 2 * d - 1 ∧
    (1 ≤ t''.items.length ∨ ∃ c0, t''.children[0]? = some c0 ∧ d ≤ c0.items.length) ∧
    (t''.items.length = t.items.length ∨ (t''.items.length + 1 = t.items.length ∧
      ∃ c1, t''.children[remIdx lt tgt t''.items]? = some c1 ∧ d ≤ c1.items.length))

theorem grow_final {lt : K → K → Prop} {d h : Nat} {tgt : Target K} {t t'' t' : Tree (V × K)}
    {out : V} {found : Bool} {z : V} (hh : 0 < h)
    (hm : GrowMid lt d h tgt t t'') (hp : RemPost lt d h tgt t'' t' out found z) :
    t'.Shape d h ∧ t'.elems = (removeOp tgt t.elems).1 ∧
      out = ((removeOp tgt t.elems).2).getD z ∧ found = ((removeOp tgt t.elems).2).isSome ∧
      t'.items.length ≤ t.items.length ∧ t.items.length ≤ t'.items.length + 1 := by
  obtain ⟨-, he, -, -, hl⟩ := hm
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hp
  rw [he] at h2 h3 h4
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · rcases hl with hl | ⟨hl, -⟩ <;> omega
  · rcases hl with hl | ⟨hl, hc⟩
    · omega
    · have := h7 hh hc; omega

/-- A node whose window (child, item, child) at `P.length` is replaced by one with the
same contents. -/
theorem grow_window {lt : K → K → Prop} {d h : Nat} (tgt : Target K)
    (P Q : List (V × K)) (Pc Qc : List (Tree (V × K))) (x x' : V × K) (a b a' b' : Tree (V × K))
    (hP : P.length = Pc.length)
    (hs : Shape d (h + 1) (.node (P ++ x :: Q) (Pc ++ a :: b :: Qc)))
    (hmax : (P ++ x :: Q).length ≤ 2 * d - 1)
    (hel : elems a' ++ x' :: elems b' = elems a ++ x :: elems b)
    (ha : (d - 1 ≤ a'.items.length ∧ a'.items.length ≤ 2 * d - 1) ∧ Shape d h a')
    (hb : (d - 1 ≤ b'.items.length ∧ b'.items.length ≤ 2 * d - 1) ∧ Shape d h b') :
    GrowMid lt d (h + 1) tgt (.node (P ++ x :: Q) (Pc ++ a :: b :: Qc))
      (.node (P ++ x' :: Q) (Pc ++ a' :: b' :: Qc)) := by
  rw [shape_succ] at hs
  refine ⟨?_, ?_, by simpa using hmax, .inl (by simp; omega), .inl (by simp)⟩
  · rw [shape_succ]
    refine ⟨by simpa using hs.1, fun c hc => ?_⟩
    simp only [List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | rfl | hc
    · exact hs.2 c (by simp [hc])
    · exact ha
    · exact hb
    · exact hs.2 c (by simp [hc])
  · simp only [elems_node]
    rw [elemsAux_split2 _ _ _ _ _ _ _ hP, elemsAux_split2 _ _ _ _ _ _ _ hP]
    have := congrArg (· ++ restAux Q Qc) hel
    simp only [List.append_assoc, List.cons_append] at this
    rw [this]

/-- Stealing from the left sibling `a` (its last item `w`, and last child) for `b`. -/
theorem steal_left {d h : Nat} (Ais Bis : List (V × K)) (Acs Bcs : List (Tree (V × K)))
    (w x : V × K) (hd : 2 ≤ d)
    (ha : (d - 1 ≤ (Ais ++ [w]).length ∧ (Ais ++ [w]).length ≤ 2 * d - 1) ∧
      Shape d h (.node (Ais ++ [w]) Acs))
    (hb : (d - 1 ≤ Bis.length ∧ Bis.length ≤ 2 * d - 1) ∧ Shape d h (.node Bis Bcs))
    (hal : d ≤ (Ais ++ [w]).length) (hbl : Bis.length ≤ d - 1) :
    elems (.node Ais Acs.dropLast) ++ w :: elems (.node (x :: Bis) (Acs.getLast?.toList ++ Bcs)) =
        elems (.node (Ais ++ [w]) Acs) ++ x :: elems (.node Bis Bcs) ∧
      ((d - 1 ≤ (Tree.node Ais Acs.dropLast).items.length ∧
          (Tree.node Ais Acs.dropLast).items.length ≤ 2 * d - 1) ∧
        Shape d h (.node Ais Acs.dropLast)) ∧
      ((d - 1 ≤ (Tree.node (x :: Bis) (Acs.getLast?.toList ++ Bcs)).items.length ∧
          (Tree.node (x :: Bis) (Acs.getLast?.toList ++ Bcs)).items.length ≤ 2 * d - 1) ∧
        Shape d h (.node (x :: Bis) (Acs.getLast?.toList ++ Bcs))) := by
  simp only [List.length_append, List.length_singleton] at ha hal
  cases h with
  | zero =>
    rw [shape_zero] at ha hb
    obtain ⟨hab, rfl⟩ := ha; obtain ⟨hbb, rfl⟩ := hb
    simp only [shape_zero, elems_node, elemsAux_nil, items_node, List.length_cons]
    refine ⟨by simp, ⟨⟨by omega, by omega⟩, by simp⟩, ⟨⟨by omega, by omega⟩, by simp⟩⟩
  | succ h =>
    rw [shape_succ] at ha hb
    rcases List.eq_nil_or_concat Acs with h0 | ⟨Acs', y, rfl⟩
    · subst h0; simp at ha
    simp only [List.concat_eq_append, List.length_append, List.length_singleton] at ha
    simp only [List.concat_eq_append, List.dropLast_concat, List.getLast?_concat,
      Option.toList_some, List.singleton_append, elems_node, items_node, List.length_cons]
    refine ⟨?_, ⟨⟨by omega, by omega⟩, ?_⟩, ⟨⟨by omega, by omega⟩, ?_⟩⟩
    · rw [elemsAux_append_item Ais [] w Acs' [y] (by omega)]
      simp
    · rw [shape_succ]
      exact ⟨by omega, fun c hc => ha.2.2 c (by simp [hc])⟩
    · rw [shape_succ]
      refine ⟨by simp; omega, fun c hc => ?_⟩
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ha.2.2 c (by simp)
      · exact hb.2.2 c hc

/-- Stealing from the right sibling `b` (its first item `w`, and first child) for `a`. -/
theorem steal_right {d h : Nat} (Ais Bis : List (V × K)) (Acs Bcs : List (Tree (V × K)))
    (w x : V × K) (hd : 2 ≤ d)
    (ha : (d - 1 ≤ Ais.length ∧ Ais.length ≤ 2 * d - 1) ∧ Shape d h (.node Ais Acs))
    (hb : (d - 1 ≤ (w :: Bis).length ∧ (w :: Bis).length ≤ 2 * d - 1) ∧
      Shape d h (.node (w :: Bis) Bcs))
    (hal : Ais.length ≤ d - 1) (hbl : d ≤ (w :: Bis).length) :
    elems (.node (Ais ++ [x]) (Acs ++ Bcs.take 1)) ++ w :: elems (.node Bis (Bcs.drop 1)) =
        elems (.node Ais Acs) ++ x :: elems (.node (w :: Bis) Bcs) ∧
      ((d - 1 ≤ (Tree.node (Ais ++ [x]) (Acs ++ Bcs.take 1)).items.length ∧
          (Tree.node (Ais ++ [x]) (Acs ++ Bcs.take 1)).items.length ≤ 2 * d - 1) ∧
        Shape d h (.node (Ais ++ [x]) (Acs ++ Bcs.take 1))) ∧
      ((d - 1 ≤ (Tree.node Bis (Bcs.drop 1)).items.length ∧
          (Tree.node Bis (Bcs.drop 1)).items.length ≤ 2 * d - 1) ∧
        Shape d h (.node Bis (Bcs.drop 1))) := by
  simp only [List.length_cons] at hb hbl
  cases h with
  | zero =>
    rw [shape_zero] at ha hb
    obtain ⟨hab, rfl⟩ := ha; obtain ⟨hbb, rfl⟩ := hb
    simp only [shape_zero, elems_node, elemsAux_nil, items_node, List.length_append,
      List.length_singleton, List.take_nil, List.drop_nil, List.append_nil]
    refine ⟨by simp, ⟨⟨by omega, by omega⟩, trivial⟩, ⟨⟨by omega, by omega⟩, trivial⟩⟩
  | succ h =>
    rw [shape_succ] at ha hb
    obtain ⟨y, Bcs', rfl⟩ : ∃ y Bcs', Bcs = y :: Bcs' := by
      cases Bcs with
      | nil => simp at hb
      | cons y Bcs' => exact ⟨y, Bcs', rfl⟩
    simp only [List.length_cons] at hb
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
      elems_node, items_node, List.length_append, List.length_singleton]
    refine ⟨?_, ⟨⟨by omega, by omega⟩, ?_⟩, ⟨⟨by omega, by omega⟩, ?_⟩⟩
    · rw [elemsAux_append_item Ais [] x Acs [y] (by omega)]
      simp
    · rw [shape_succ]
      refine ⟨by simp; omega, fun c hc => ?_⟩
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact ha.2.2 c hc
      · exact hb.2.2 c (by simp)
    · rw [shape_succ]
      exact ⟨by omega, fun c hc => hb.2.2 c (by simp [hc])⟩

/-- Merging `a`, the item `x` and `b` into one child. -/
theorem merge_trees {d h : Nat} (Ais Bis : List (V × K)) (Acs Bcs : List (Tree (V × K)))
    (x : V × K) (hd : 2 ≤ d)
    (ha : (d - 1 ≤ Ais.length ∧ Ais.length ≤ 2 * d - 1) ∧ Shape d h (.node Ais Acs))
    (hb : (d - 1 ≤ Bis.length ∧ Bis.length ≤ 2 * d - 1) ∧ Shape d h (.node Bis Bcs))
    (hal : Ais.length ≤ d - 1) (hbl : Bis.length ≤ d - 1) :
    elems (.node (Ais ++ x :: Bis) (Acs ++ Bcs)) = elems (.node Ais Acs) ++ x :: elems (.node Bis Bcs) ∧
      ((d - 1 ≤ (Tree.node (Ais ++ x :: Bis) (Acs ++ Bcs)).items.length ∧
          (Tree.node (Ais ++ x :: Bis) (Acs ++ Bcs)).items.length ≤ 2 * d - 1) ∧
        Shape d h (.node (Ais ++ x :: Bis) (Acs ++ Bcs))) ∧
      d ≤ (Tree.node (Ais ++ x :: Bis) (Acs ++ Bcs)).items.length := by
  simp only [items_node, List.length_append, List.length_cons]
  cases h with
  | zero =>
    rw [shape_zero] at ha hb
    obtain ⟨hab, rfl⟩ := ha; obtain ⟨hbb, rfl⟩ := hb
    simp only [shape_zero, elems_node, elemsAux_nil, List.append_nil]
    exact ⟨by simp, ⟨⟨by omega, by omega⟩, trivial⟩, by omega⟩
  | succ h =>
    rw [shape_succ] at ha hb
    simp only [elems_node]
    refine ⟨elemsAux_append_item _ _ _ _ _ ha.2.1, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
    rw [shape_succ]
    refine ⟨by simp; omega, fun c hc => ?_⟩
    rcases List.mem_append.1 hc with hc | hc
    · exact ha.2.2 c hc
    · exact hb.2.2 c hc

theorem grow_merge {lt : K → K → Prop} {d h : Nat} (tgt : Target K)
    (P Q : List (V × K)) (Pc Qc : List (Tree (V × K))) (x : V × K) (a b m : Tree (V × K))
    (hP : P.length = Pc.length)
    (hs : Shape d (h + 1) (.node (P ++ x :: Q) (Pc ++ a :: b :: Qc)))
    (hmax : (P ++ x :: Q).length ≤ 2 * d - 1)
    (hel : elems m = elems a ++ x :: elems b)
    (hm : ((d - 1 ≤ m.items.length ∧ m.items.length ≤ 2 * d - 1) ∧ Shape d h m) ∧
      d ≤ m.items.length)
    (hidx : remIdx lt tgt (P ++ Q) = P.length) :
    GrowMid lt d (h + 1) tgt (.node (P ++ x :: Q) (Pc ++ a :: b :: Qc))
      (.node (P ++ Q) (Pc ++ m :: Qc)) := by
  rw [shape_succ] at hs
  have hget : (Pc ++ m :: Qc)[P.length]? = some m := by
    rw [hP, List.getElem?_append_right (Nat.le_refl _)]; simp
  refine ⟨?_, ?_, by simp at hmax ⊢; omega, ?_, .inr ⟨by simp; omega, m, by simpa [hidx] using hget, hm.2⟩⟩
  · rw [shape_succ]
    refine ⟨by simp at hs ⊢; omega, fun c hc => ?_⟩
    simp only [List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | hc
    · exact hs.2 c (by simp [hc])
    · exact hm.1
    · exact hs.2 c (by simp [hc])
  · simp only [elems_node]
    rw [elemsAux_split1 _ _ _ _ _ hP, elemsAux_split2 _ _ _ _ _ _ _ hP, hel]
    simp
  · by_cases hP0 : P = []
    · subst hP0
      refine .inr ⟨m, ?_, hm.2⟩
      simpa using hget
    · exact .inl (by simp; have := List.length_pos_iff.2 hP0; omega)

/-- `remove` descends into the merged child. -/
theorem merge_remIdx {lt : K → K → Prop} (ord : StrictOrder lt) (tgt : Target K)
    (P Q : List (V × K)) (x : V × K) (hsort : Sorted lt (P ++ x :: Q))
    (h : remIdx lt tgt (P ++ x :: Q) = P.length ∨
      (remIdx lt tgt (P ++ x :: Q) = P.length + 1 ∧ Q = [])) :
    remIdx lt tgt (P ++ Q) = P.length := by
  cases tgt with
  | min => simp only [remIdx] at h ⊢; omega
  | max =>
    simp only [remIdx, List.length_append, List.length_cons] at h ⊢
    rcases h with h | ⟨-, rfl⟩
    · omega
    · simp
  | key k =>
    simp only [remIdx] at h ⊢
    rw [countLt_eq_iff]
    rcases h with h | ⟨h, rfl⟩
    · obtain ⟨-, hlt, hge⟩ := (countLt_eq_iff _ k _).1 h
      refine ⟨by simp, fun m hm hm' => ?_, fun hl => ?_⟩
      · have := hlt m hm (by simp; omega)
        rwa [List.getElem_append_left hm] at this ⊢
      · have hx := hge (by simp)
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem_cons_zero] at hx
        rw [List.getElem_append_right (Nat.le_refl _)]
        have hq := (sorted_mid hsort).2 _ (List.getElem_mem (l := Q) (by simp at hl; omega))
        intro hq'
        exact hx (ord.trans _ _ _ hq (by simpa using hq'))
    · obtain ⟨-, hlt, -⟩ := (countLt_eq_iff _ k _).1 h
      refine ⟨by simp, fun m hm hm' => ?_, fun hl => by simp at hl⟩
      have := hlt m (by omega) (by simp; omega)
      rw [List.getElem_append_left (by simpa using hm)] at this; simpa using this

end grow

/-! ## `removeOp` on the whole tree (`deleteItem`) -/

section whole
variable {V K : Type} {lt : K → K → Prop}

@[simp] theorem removeOp_nil (tgt : Target K) :
    removeOp tgt ([] : List (V × K)) = ([], none) := by
  cases tgt <;> simp [removeOp, delete, lookup]

theorem removeOp_sublist (tgt : Target K) (s : List (V × K)) : (removeOp tgt s).1.Sublist s := by
  cases tgt with
  | key k => exact List.filter_sublist
  | min => exact List.tail_sublist s
  | max => exact List.dropLast_sublist s

theorem removeOp_none (tgt : Target K) (s : List (V × K))
    (h : (removeOp tgt s).2.isSome = false) : (removeOp tgt s).1 = s := by
  cases tgt with
  | key k =>
    simp only [removeOp, lookup, Option.isSome_map, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none, List.find?_eq_none] at h ⊢
    exact delete_of_ne s k (fun e he hk => by simpa [hk] using h e he)
  | min => cases s <;> simp_all [removeOp]
  | max =>
    simp only [removeOp, Option.isSome_map, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none, List.getLast?_eq_none_iff] at h ⊢
    subst h; rfl

theorem removeOp_some (ord : StrictOrder lt) (tgt : Target K) (s : List (V × K))
    (hs : Sorted lt s) (h : (removeOp tgt s).2.isSome = true) :
    (removeOp tgt s).1.length + 1 = s.length := by
  cases tgt with
  | key k =>
    simp only [removeOp, lookup, Option.isSome_map, Option.isSome_iff_exists,
      List.find?_eq_some_iff_append] at h ⊢
    obtain ⟨e, he, A, B, rfl, -⟩ := h
    have hek : e.2 = k := by simpa using he
    have hm := sorted_mid hs
    rw [hek] at hm
    rw [delete_append, delete_of_ne _ k (fun x hx => ne_of_lt' (o := ord) (hm.1 x hx)),
      show e :: B = [e] ++ B from rfl, delete_append,
      delete_of_ne _ k (fun x hx => (ne_of_lt' (o := ord) (hm.2 x hx)).symm)]
    simp [delete, hek]; omega
  | min =>
    cases s with
    | nil => simp [removeOp] at h
    | cons x s => simp [removeOp]
  | max =>
    cases s with
    | nil => simp [removeOp] at h
    | cons x s => simp [removeOp]

end whole

/-! ## Node resources -/

section iris
open Iris Iris.BI Iris.ProofMode github_com.google.btree
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {K : Type}
variable (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc)

theorem ownNodes_of_frozenList' (dq : DFrac) :
    ∀ (ps : List Loc) (ts : List (Tree (V × K))),
      frozenList o c f less ps ts ⊢ ownNodes o c f less dq ps ts
  | [], [] => by rw [frozenList_nil, ownNodes_nil]
  | p :: ps, t :: ts => by
    rw [frozenList_cons, ownNodes_cons]
    iintro ⟨H1, H2⟩
    isplitl [H1]
    · iapply ownNode_of_frozen; iexact H1
    · iapply ownNodes_of_frozenList' dq ps ts $$ H2
  | [], _ :: _ => by rw [frozenList]; iintro %h; exact h.elim
  | _ :: _, [] => by rw [frozenList]; iintro %h; exact h.elim

/-- Reading the length of a subtree's item slice. -/
theorem ownNode_len_acc (dq : DFrac) (p : Loc) (t : Tree (V × K)) :
    ownNode o c f less dq p t ⊢ ∃ (isl : GoSlice) (dq' : DFrac),
      structFieldRef (node V) go!"items" p ↦{dq'} isl ∗ ⌜t.items.length = sint.nat isl.len⌝ ∗
      (structFieldRef (node V) go!"items" p ↦{dq'} isl -∗ ownNode o c f less dq p t) := by
  cases t with
  | node is cs =>
  iintro H
  icases (ownNode_unfold o c f less dq p _).1 $$ H with (Hown | #Hfr)
  · unfold ownedNode nodeShallow nodeFields
    icases Hown with ⟨%ps, ⟨%isl, %csl, ⟨%Hnn, Hi, Hc, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩, Hch⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hisl
    iexists isl, dq
    iframe Hi
    isplitr
    · ipureintro; simpa using Hl.1
    iintro Hi
    iapply ownNode_of_owned
    unfold ownedNode nodeShallow nodeFields
    iexists ps
    iframe
    ipureintro; exact Hnn
  · ihave Hfr2 := Hfr
    rw [frozen_node]
    unfold nodeFields
    icases Hfr2 with ⟨%isl, %csl, %cow, %ps, ⟨%Hnn, #Hi, #Hc, #Hw⟩, %Hne, #Hcow, #Hisl, #Hcsl, #Hfl⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hisl
    iexists isl, DFrac.discard
    iframe Hi
    isplitr
    · ipureintro; simpa using Hl.1
    iintro _
    iapply ownNode_of_frozen
    rw [frozen_node]; unfold nodeFields
    iexact Hfr

/-- Reading the length of a subtree's item slice. -/
theorem ownNode_len_acc' (dq : DFrac) (p : Loc) (t : Tree (V × K)) :
    ownNode o c f less dq p t ⊢ ∃ (isl : GoSlice) (dq' : DFrac),
      structFieldRef (node V) go!"items" p ↦{dq'} isl ∗ ⌜t.items.length = sint.nat isl.len ∧ 0 ≤ sint.Z isl.len⌝ ∗
      (structFieldRef (node V) go!"items" p ↦{dq'} isl -∗ ownNode o c f less dq p t) := by
  cases t with
  | node is cs =>
  iintro H
  icases (ownNode_unfold o c f less dq p _).1 $$ H with (Hown | #Hfr)
  · unfold ownedNode nodeShallow nodeFields
    icases Hown with ⟨%ps, ⟨%isl, %csl, ⟨%Hnn, Hi, Hc, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩, Hch⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hisl
    iexists isl, dq
    iframe Hi
    isplitr
    · ipureintro; exact ⟨by simpa using Hl.1, Hl.2⟩
    iintro Hi
    iapply ownNode_of_owned
    unfold ownedNode nodeShallow nodeFields
    iexists ps
    iframe
    ipureintro; exact Hnn
  · ihave Hfr2 := Hfr
    rw [frozen_node]
    unfold nodeFields
    icases Hfr2 with ⟨%isl, %csl, %cow, %ps, ⟨%Hnn, #Hi, #Hc, #Hw⟩, %Hne, #Hcow, #Hisl, #Hcsl, #Hfl⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hisl
    iexists isl, DFrac.discard
    iframe Hi
    isplitr
    · ipureintro; exact ⟨by simpa using Hl.1, Hl.2⟩
    iintro _
    iapply ownNode_of_frozen
    rw [frozen_node]; unfold nodeFields
    iexact Hfr

/-- An owned node's resources. -/
def ownedRes (dq : DFrac) (n : Loc) (is : List (V × K)) (cs : List (Tree (V × K)))
    (ps : List Loc) (isl csl : GoSlice) : IProp GF :=
  iprop(⌜n ≠ null⌝ ∗
    structFieldRef (node V) go!"items" n ↦{dq} isl ∗
    structFieldRef (node V) go!"children" n ↦{dq} csl ∗
    structFieldRef (node V) go!"cow" n ↦{dq} c ∗
    isl ↦*{dq} is.map Prod.fst ∗ ownSliceCap V isl dq ∗
    csl ↦*{dq} ps ∗ ownSliceCap Loc csl dq ∗
    ownNodes o c f less dq ps cs)

theorem ownedNode_open (dq : DFrac) (n : Loc) (is : List (V × K)) (cs : List (Tree (V × K))) :
    ownedNode o c f less dq n (.node is cs) ⊢
      ∃ ps isl csl, ownedRes o c f less dq n is cs ps isl csl := by
  unfold ownedNode nodeShallow nodeFields ownedRes
  iintro ⟨%ps, ⟨%isl, %csl, ⟨%Hnn, Hi, Hc, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩, Hch⟩
  iexists ps, isl, csl
  simp only [Tree.items_node, Tree.children_node]
  iframe
  ipureintro; exact Hnn

theorem ownedNode_close (dq : DFrac) (n : Loc) (is : List (V × K)) (cs : List (Tree (V × K)))
    (ps : List Loc) (isl csl : GoSlice) :
    ownedRes o c f less dq n is cs ps isl csl ⊢ ownedNode o c f less dq n (.node is cs) := by
  unfold ownedNode nodeShallow nodeFields ownedRes
  iintro ⟨%Hnn, Hi, Hc, Hw, Hisl, Hicap, Hcsl, Hccap, Hch⟩
  iexists ps
  simp only [Tree.items_node, Tree.children_node]
  iframe
  ipureintro; exact Hnn

theorem ownNode_ne_null (dq : DFrac) (p : Loc) (t : Tree (V × K)) :
    ownNode o c f less dq p t ⊢ ⌜p ≠ null⌝ := by
  cases t with
  | node is cs =>
  iintro H
  icases (ownNode_unfold o c f less dq p _).1 $$ H with (Hown | #Hfr)
  · unfold ownedNode nodeShallow nodeFields
    icases Hown with ⟨%ps, ⟨%isl, %csl, ⟨%Hnn, -⟩, -⟩, -⟩
    ipureintro; exact Hnn
  · rw [frozen_node]
    unfold nodeFields
    icases Hfr with ⟨%isl, %csl, %cow, %ps, ⟨%Hnn, -⟩, -⟩
    ipureintro; exact Hnn

theorem ownNodes_split1 (dq : DFrac) (Pp Qp : List Loc) (Pc Qc : List (Tree (V × K)))
    (a : Loc) (ta : Tree (V × K)) (hP : Pp.length = Pc.length) :
    ownNodes o c f less dq (Pp ++ a :: Qp) (Pc ++ ta :: Qc) ⊣⊢
      ownNodes o c f less dq Pp Pc ∗ ownNode o c f less dq a ta ∗
        ownNodes o c f less dq Qp Qc := by
  refine (ownNodes_app o c f less dq _ _ _ _ hP).trans ?_
  rw [ownNodes_cons]; exact .rfl

theorem ownNodes_split2 (dq : DFrac) (Pp Qp : List Loc) (Pc Qc : List (Tree (V × K)))
    (a b : Loc) (ta tb : Tree (V × K)) (hP : Pp.length = Pc.length) :
    ownNodes o c f less dq (Pp ++ a :: b :: Qp) (Pc ++ ta :: tb :: Qc) ⊣⊢
      ownNodes o c f less dq Pp Pc ∗ ownNode o c f less dq a ta ∗ ownNode o c f less dq b tb ∗
        ownNodes o c f less dq Qp Qc := by
  refine (ownNodes_split1 o c f less dq _ _ _ _ a ta hP).trans ?_
  rw [ownNodes_cons]; exact .rfl

/-- What `freeNode` takes. -/
def freePre (n : Loc) : IProp GF :=
  iprop((∃ (is : List (V × K)) (ps : List Loc), nodeShallow (V := V) c (DFrac.own 1) n is ps) ∨
    ∃ t : Tree (V × K), frozen o c f less n t)

/-- Reading the node merged away (owned or frozen), and handing it to `freeNode`. -/
theorem ownNode_merge_acc (p : Loc) (bis : List (V × K)) (bcs : List (Tree (V × K))) :
    ownNode o c f less (DFrac.own 1) p (.node bis bcs) ⊢
      ∃ (bisl bcsl : GoSlice) (dq : DFrac) (bps : List Loc),
        structFieldRef (node V) go!"items" p ↦{dq} bisl ∗
        structFieldRef (node V) go!"children" p ↦{dq} bcsl ∗
        bisl ↦*{dq} bis.map Prod.fst ∗ bcsl ↦*{dq} bps ∗
        ownNodes o c f less (DFrac.own 1) bps bcs ∗
        ((structFieldRef (node V) go!"items" p ↦{dq} bisl ∗
          structFieldRef (node V) go!"children" p ↦{dq} bcsl ∗
          bisl ↦*{dq} bis.map Prod.fst ∗ bcsl ↦*{dq} bps) -∗ freePre o c f less p) := by
  iintro H
  icases (ownNode_unfold o c f less _ p _).1 $$ H with (Hown | #Hfr)
  · unfold ownedNode nodeShallow nodeFields
    icases Hown with ⟨%ps, ⟨%isl, %csl, ⟨%Hnn, Hi, Hc, Hw⟩, Hisl, Hicap, Hcsl, Hccap⟩, Hch⟩
    iexists isl, csl, DFrac.own 1, ps
    simp only [Tree.items_node, Tree.children_node]
    iframe Hi Hc Hisl Hcsl Hch
    iintro ⟨Hi, Hc, Hisl, Hcsl⟩
    unfold freePre
    ileft
    iexists bis, ps
    unfold nodeShallow nodeFields
    iexists isl, csl
    iframe
    ipureintro; exact Hnn
  · ihave Hfr2 := Hfr
    rw [frozen_node]
    unfold nodeFields
    icases Hfr2 with ⟨%isl, %csl, %cow, %ps, ⟨%Hnn, #Hi, #Hc, #Hw⟩, %Hne, #Hcow, #Hisl, #Hcsl, #Hfl⟩
    iexists isl, csl, DFrac.discard, ps
    iframe Hi Hc Hisl Hcsl
    isplitl
    · iapply ownNodes_of_frozenList' o c f less _ ps bcs $$ Hfl
    iintro _
    unfold freePre
    iright
    iexists (.node bis bcs)
    rw [frozen_node]; unfold nodeFields
    iexact Hfr

theorem isCow_less_rm (cw : Loc) :
    isCow o cw f less ⊢ structFieldRef (copyOnWriteContext V) go!"less" cw ↦□ less := by
  unfold isCow
  iintro ⟨Hc, _, _⟩
  iStructNamed Hc
  iexact less

theorem isCow_isLess_rm (cw : Loc) : isCow o cw f less ⊢ isLess o less := by
  unfold isCow
  iintro ⟨_, _, H⟩
  iexact H

theorem allItems_mono_rm {l1 l2 : List (V × K)} (h : ∀ e ∈ l1, e ∈ l2) :
    allItems o l2 ⊢ allItems o l1 := by
  unfold allItems
  iintro #H
  imodintro
  iintro %e %he
  iapply H
  ipureintro; exact h e he

end iris

end RemoveLemmas

end Btree
end EtcdGrove
end Perennial
