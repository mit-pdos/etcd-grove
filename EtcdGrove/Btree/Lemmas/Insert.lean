/-
Pure lemmas for `node.insert` and `ReplaceOrInsert`: `insert` and `lookup` on sorted
lists split around the inserted key, the in-order contents of a node around one of its
items or children, splitting a child, and the shape facts.
-/
import EtcdGrove.Btree.Model
import EtcdGrove.Btree.NodeLemmas

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree
/-! Everything here is in `Btree.InsertLemmas` (other groups' lemma files use some of the same
names). -/
namespace InsertLemmas

open Classical Tree

private theorem ifP {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]
private theorem ifN {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

section lists
variable {V K : Type} {lt : K → K → Prop}

theorem _root_.Perennial.EtcdGrove.Btree.StrictOrder.ins_asymm {lt : K → K → Prop} (ho : StrictOrder lt) {a b : K} (h : lt a b) :
    ¬ lt b a := fun h' => ho.irrefl a (ho.trans _ _ _ h h')

theorem _root_.Perennial.EtcdGrove.Btree.StrictOrder.ins_ne {lt : K → K → Prop} (ho : StrictOrder lt) {a b : K} (h : lt a b) :
    a ≠ b := by rintro rfl; exact ho.irrefl a h

/-! ### `insert` -/

theorem insert_app_left (ho : StrictOrder lt) (A X : List (V × K)) (e : V × K)
    (hA : ∀ a ∈ A, lt a.2 e.2) : insert lt (A ++ X) e = A ++ insert lt X e := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    have h1 : lt a.2 e.2 := hA a (by simp)
    have h2 : ¬ lt e.2 a.2 := ho.ins_asymm h1
    have h3 : e.2 ≠ a.2 := fun h => ho.ins_ne h1 h.symm
    simp only [List.cons_append, insert, h2, h3, ↓reduceIte,
      ih (fun b hb => hA b (by simp [hb]))]

theorem insert_app_right (X B : List (V × K)) (e : V × K)
    (hB : ∀ b ∈ B, lt e.2 b.2) : insert lt (X ++ B) e = insert lt X e ++ B := by
  induction X with
  | nil =>
    cases B with
    | nil => rfl
    | cons b B =>
      simp [insert, hB b (by simp)]
  | cons x X ih =>
    simp only [List.cons_append, insert]
    by_cases h1 : lt e.2 x.2
    · simp [h1]
    · by_cases h2 : e.2 = x.2
      · simp only [h1, ↓reduceIte]
        simp [h2]
      · simp only [h1, h2, ↓reduceIte, ih, List.cons_append]

theorem insert_mid (ho : StrictOrder lt) (L M R : List (V × K)) (e : V × K)
    (hL : ∀ a ∈ L, lt a.2 e.2) (hR : ∀ b ∈ R, lt e.2 b.2) :
    insert lt (L ++ M ++ R) e = L ++ insert lt M e ++ R := by
  rw [List.append_assoc, insert_app_left ho _ _ _ hL, insert_app_right _ _ _ hR,
    List.append_assoc]

theorem insert_split (ho : StrictOrder lt) (A B : List (V × K)) (e : V × K)
    (hA : ∀ a ∈ A, lt a.2 e.2) (hB : ∀ b ∈ B, lt e.2 b.2) :
    insert lt (A ++ B) e = A ++ e :: B := by
  have := insert_mid ho A [] B e hA hB
  simpa [insert] using this

theorem insert_replace (ho : StrictOrder lt) (A B : List (V × K)) (x e : V × K)
    (hA : ∀ a ∈ A, lt a.2 e.2) (hx : x.2 = e.2) :
    insert lt (A ++ x :: B) e = A ++ e :: B := by
  rw [insert_app_left ho _ _ _ hA]
  have h1 : ¬ lt e.2 x.2 := hx ▸ ho.irrefl _
  simp only [insert, h1, ↓reduceIte]
  simp [hx]

/-! ### `lookup` -/

theorem lookup_app_left (A X : List (V × K)) (k : K) (hA : ∀ a ∈ A, a.2 ≠ k) :
    lookup (A ++ X) k = lookup X k := by
  unfold lookup
  rw [List.find?_append, List.find?_eq_none.2 (by intro a ha; simpa using hA a ha)]
  rfl

theorem lookup_app_right (X B : List (V × K)) (k : K) (hB : ∀ b ∈ B, b.2 ≠ k) :
    lookup (X ++ B) k = lookup X k := by
  unfold lookup
  rw [List.find?_append, (List.find?_eq_none (l := B)).2 (by intro a ha; simpa using hB a ha)]
  simp

theorem lookup_cons_eq (x : V × K) (B : List (V × K)) (k : K) (hx : x.2 = k) :
    lookup (x :: B) k = some x.1 := by
  simp [lookup, hx]

theorem lookup_nil (k : K) : lookup ([] : List (V × K)) k = none := rfl

/-! ### Sorted lists -/

theorem sorted_mid {lt : K → K → Prop} {A B : List (V × K)} {x : V × K}
    (hs : Sorted lt (A ++ x :: B)) : (∀ a ∈ A, lt a.2 x.2) ∧ (∀ b ∈ B, lt x.2 b.2) := by
  unfold Sorted at hs
  rw [List.pairwise_append, List.pairwise_cons] at hs
  exact ⟨fun a ha => hs.2.2 a ha x (by simp), hs.2.1.1⟩

theorem sorted_sublist {lt : K → K → Prop} {l l' : List (V × K)} (h : l.Sublist l')
    (hs : Sorted lt l') : Sorted lt l := List.Pairwise.sublist h hs

theorem sorted_getElem {lt : K → K → Prop} {l : List (V × K)} (hs : Sorted lt l)
    {i j : Nat} {a b : V × K} (hij : i < j) (ha : l[i]? = some a) (hb : l[j]? = some b) :
    lt a.2 b.2 := by
  rcases List.getElem?_eq_some_iff.1 ha with ⟨hi, rfl⟩
  rcases List.getElem?_eq_some_iff.1 hb with ⟨hj, rfl⟩
  exact List.pairwise_iff_getElem.1 hs i j hi hj hij

/-- The keys `items.find` separates: below `countLt` they are less than `k`. -/
theorem countLt_lo (is : List (V × K)) (k : K) :
    ∀ j a, j < countLt lt is k → is[j]? = some a → lt a.2 k := by
  intro j a hj ha
  unfold countLt at hj
  have he : is[j]? = (is.takeWhile (fun e => decide (lt e.2 k)) ++
      is.dropWhile (fun e => decide (lt e.2 k)))[j]? := by
    rw [List.takeWhile_append_dropWhile]
  rw [he, List.getElem?_append_left hj] at ha
  have hm := List.mem_of_getElem? ha
  have hall := List.all_takeWhile (l := is) (p := fun e => decide (lt e.2 k))
  rw [List.all_eq_true] at hall
  simpa using hall a hm

theorem countLt_le (is : List (V × K)) (k : K) : countLt lt is k ≤ is.length :=
  (List.takeWhile_sublist _).length_le

/-- Not found: from `countLt` on, the keys are greater than `k`. -/
theorem countLt_hi (ho : StrictOrder lt) (is : List (V × K)) (k : K) (hs : Sorted lt is)
    (hnf : ∀ e, is[countLt lt is k]? = some e → e.2 ≠ k) :
    ∀ j a, countLt lt is k ≤ j → is[j]? = some a → lt k a.2 := by
  have h0 : ∀ e, is[countLt lt is k]? = some e → lt k e.2 := by
    intro e hie
    have he : is[countLt lt is k]? = (is.takeWhile (fun e => decide (lt e.2 k)) ++
        is.dropWhile (fun e => decide (lt e.2 k)))[countLt lt is k]? := by
      rw [List.takeWhile_append_dropWhile]
    have hd : (is.dropWhile (fun e => decide (lt e.2 k)))[0]? = some e := by
      rw [he, List.getElem?_append_right (by unfold countLt; omega)] at hie
      simpa [countLt] using hie
    have hne : is.dropWhile (fun e => decide (lt e.2 k)) ≠ [] := by
      intro h; rw [h] at hd; simp at hd
    have hhd := List.head_dropWhile_not (fun (e : V × K) => decide (lt e.2 k)) hne
    rw [List.head_eq_getElem] at hhd
    rw [List.getElem?_eq_getElem (by
      rcases List.getElem?_eq_some_iff.1 hd with ⟨h, _⟩; exact h)] at hd
    rw [Option.some.inj hd] at hhd
    have hlt : ¬ lt e.2 k := by simpa using hhd
    rcases ho.total e.2 k with h | h | h
    · exact absurd h hlt
    · exact absurd h (hnf e hie)
    · exact h
  intro j a hj ha
  rcases Nat.lt_or_eq_of_le hj with hj | rfl
  · have hi : countLt lt is k < is.length := by
      rcases List.getElem?_eq_some_iff.1 ha with ⟨h, _⟩; omega
    obtain ⟨e, hie⟩ : ∃ e, is[countLt lt is k]? = some e := ⟨_, List.getElem?_eq_getElem hi⟩
    exact ho.trans _ _ _ (h0 e hie) (sorted_getElem hs hj hie ha)
  · exact h0 a ha

end lists

section trees
variable {E : Type}

theorem elemsAux_append : ∀ (is1 is2 : List E) (cs1 cs2 : List (Tree E)),
    is1.length = cs1.length →
    elemsAux (is1 ++ is2) (cs1 ++ cs2) = elemsAux is1 cs1 ++ elemsAux is2 cs2
  | [], is2, [], cs2, _ => by simp
  | x :: is1, is2, c :: cs1, cs2, h => by
    simp only [List.cons_append, elemsAux_cons_cons,
      elemsAux_append is1 is2 cs1 cs2 (by simpa using h), List.append_assoc]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h

theorem elemsAux_cons_child (D : List E) (c : Tree E) (rest : List (Tree E)) :
    elemsAux D (c :: rest) = c.elems ++ (D.take 1 ++ elemsAux D.tail rest) := by
  cases D <;> simp

theorem items_sublist : ∀ (is : List E) (cs : List (Tree E)), is.Sublist (elemsAux is cs)
  | is, [] => by simp
  | [], _ :: _ => List.nil_sublist _
  | i :: is, c :: cs => by
    rw [elemsAux_cons_cons]
    exact ((items_sublist is cs).cons_cons i).trans (List.sublist_append_right _ _)

/-- The contents around item `i`, which can be replaced. -/
theorem elemsAux_item : ∀ (is : List E) (cs : List (Tree E)) (i : Nat) (x : E),
    is[i]? = some x →
    ∃ A B, elemsAux is cs = A ++ x :: B ∧ ∀ e, elemsAux (is.set i e) cs = A ++ e :: B
  | is, [], i, x, hx => by
    have hi : i < is.length := by
      rcases List.getElem?_eq_some_iff.1 hx with ⟨h, _⟩; exact h
    refine ⟨is.take i, is.drop (i + 1), ?_, ?_⟩
    · rw [List.getElem?_eq_getElem hi] at hx
      rw [elemsAux_nil, ← Option.some.inj hx, List.getElem_cons_drop, List.take_append_drop]
    · intro e; rw [elemsAux_nil, List.set_eq_take_append_cons_drop]; simp [hi]
  | [], _ :: _, _, _, hx => by simp at hx
  | y :: is, c :: cs, 0, x, hx => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    exact ⟨c.elems, elemsAux is cs, by simp, fun e => by simp⟩
  | y :: is, c :: cs, i + 1, x, hx => by
    simp only [List.getElem?_cons_succ] at hx
    obtain ⟨A, B, h1, h2⟩ := elemsAux_item is cs i x hx
    exact ⟨c.elems ++ y :: A, B, by simp [h1], fun e => by simp [h2]⟩

/-- The contents around child `i`, which can be replaced. -/
theorem elemsAux_child : ∀ (is : List E) (cs : List (Tree E)) (i : Nat),
    cs.length = is.length + 1 → i < cs.length →
    ∃ L R, (∀ c, elemsAux is (cs.set i c) = L ++ c.elems ++ R) ∧
      (L = [] ∨ ∃ L' a j, L = L' ++ [a] ∧ j < i ∧ is[j]? = some a) ∧
      (R = [] ∨ ∃ R' b j, R = b :: R' ∧ i ≤ j ∧ is[j]? = some b)
  | [], [c0], 0, _, _ => ⟨[], [], fun c => by simp, .inl rfl, .inl rfl⟩
  | [], [], _, h, _ => by simp at h
  | [], _ :: _ :: _, _, h, _ => by simp at h
  | [], [_], _ + 1, _, h => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | x :: is, c0 :: cs, 0, _, _ =>
    ⟨[], x :: elemsAux is cs, fun c => by simp, .inl rfl,
      .inr ⟨_, x, 0, rfl, Nat.le_refl _, rfl⟩⟩
  | x :: is, c0 :: cs, i + 1, hl, hi => by
    obtain ⟨L, R, h1, hL, hR⟩ :=
      elemsAux_child is cs i (by simpa using hl) (by simpa using hi)
    refine ⟨c0.elems ++ x :: L, R, fun c => by simp [h1], ?_, ?_⟩
    · right
      rcases hL with rfl | ⟨L', a, j, rfl, hj, ha⟩
      · exact ⟨c0.elems, x, 0, by simp, by omega, rfl⟩
      · exact ⟨c0.elems ++ x :: L', a, j + 1, by simp, by omega, by simpa using ha⟩
    · rcases hR with rfl | ⟨R', b, j, rfl, hj, hb⟩
      · exact .inl rfl
      · exact .inr ⟨R', b, j + 1, rfl, by omega, by simpa using hb⟩

/-- A node's contents with child `m`... -/
theorem elemsAux_split (m : Nat) : ∀ (cis : List E) (ccs : List (Tree E)) (e : E),
    cis[m]? = some e → (ccs = [] ∨ ccs.length = cis.length + 1) →
    elemsAux cis ccs = elemsAux (cis.take m) (ccs.take (m + 1)) ++
      e :: elemsAux (cis.drop (m + 1)) (ccs.drop (m + 1)) := by
  induction m with
  | zero =>
    intro cis ccs e he hc
    match cis, ccs, hc with
    | [], _, _ => simp at he
    | x :: xs, [], _ =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he; subst he; simp
    | x :: xs, c :: cs, _ =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he; subst he; simp
  | succ m ih =>
    intro cis ccs e he hc
    match cis, ccs, hc with
    | [], _, _ => simp at he
    | x :: xs, [], _ =>
      simp only [elemsAux_nil, List.take_nil, List.drop_nil]
      rw [List.getElem?_eq_some_iff] at he
      obtain ⟨hlt, rfl⟩ := he
      rw [List.getElem_cons_drop, List.take_append_drop]
    | x :: xs, c :: cs, hc =>
      have hc' : cs = [] ∨ cs.length = xs.length + 1 := by
        rcases hc with h | h
        · simp at h
        · right; simpa using h
      simp only [List.getElem?_cons_succ] at he
      simp only [List.take_succ_cons, List.drop_succ_cons, elemsAux_cons_cons,
        ih xs cs e he hc', List.cons_append, List.append_assoc]

/-- Splitting child `i` (around its item `m`, which moves up) keeps the contents. -/
theorem elemsAux_splitChild (is : List E) (cs : List (Tree E)) (i m : Nat)
    (cis : List E) (ccs : List (Tree E)) (e : E)
    (hl : cs.length = is.length + 1) (hci : cs[i]? = some (.node cis ccs))
    (he : cis[m]? = some e) (hc : ccs = [] ∨ ccs.length = cis.length + 1) :
    elemsAux (is.take i ++ e :: is.drop i)
      (cs.take i ++ .node (cis.take m) (ccs.take (m + 1)) ::
        .node (cis.drop (m + 1)) (ccs.drop (m + 1)) :: cs.drop (i + 1)) =
    elemsAux is cs := by
  have hi : i < cs.length := by
    rcases List.getElem?_eq_some_iff.1 hci with ⟨h, _⟩; exact h
  have hcs : cs = cs.take i ++ Tree.node cis ccs :: cs.drop (i + 1) := by
    rw [List.getElem?_eq_getElem hi] at hci
    rw [← Option.some.inj hci, List.getElem_cons_drop, List.take_append_drop]
  have hlen : (is.take i).length = (cs.take i).length := by simp; omega
  conv => rhs; rw [hcs, ← List.take_append_drop i is]
  rw [elemsAux_append _ _ _ _ hlen, elemsAux_append _ _ _ _ hlen]
  congr 1
  simp only [elemsAux_cons_child, elems_node]
  rw [elemsAux_split m cis ccs e he hc]
  simp

end trees

section insert
variable {V K : Type} {lt : K → K → Prop}

theorem lookup_none (l : List (V × K)) (k : K) (h : ∀ a ∈ l, a.2 ≠ k) : lookup l k = none := by
  have := lookup_app_left l [] k h
  rw [List.append_nil] at this
  rw [this]; rfl

/-- Descending into child `i`, whose keys are between those of items `i - 1` and `i`. -/
theorem descend_child (ho : StrictOrder lt) (is : List (V × K)) (cs : List (Tree (V × K)))
    (i : Nat) (ci : Tree (V × K)) (k : K)
    (hl : cs.length = is.length + 1) (hci : cs[i]? = some ci) (hs : Sorted lt (elemsAux is cs))
    (hlo : ∀ j a, j < i → is[j]? = some a → lt a.2 k)
    (hhi : ∀ j a, i ≤ j → is[j]? = some a → lt k a.2) :
    Sorted lt ci.elems ∧ (∀ x ∈ ci.elems, x ∈ elemsAux is cs) ∧
      lookup (elemsAux is cs) k = lookup ci.elems k ∧
      ∀ (c' : Tree (V × K)) (v : V), c'.elems = insert lt ci.elems (v, k) →
        elemsAux is (cs.set i c') = insert lt (elemsAux is cs) (v, k) := by
  have hi : i < cs.length := by
    rcases List.getElem?_eq_some_iff.1 hci with ⟨h, _⟩; exact h
  obtain ⟨L, R, h1, hL, hR⟩ := elemsAux_child is cs i hl hi
  have hset : cs.set i ci = cs := by
    rw [List.getElem?_eq_getElem hi] at hci
    rw [← Option.some.inj hci, List.set_getElem_self]
  have he : elemsAux is cs = L ++ ci.elems ++ R := by rw [← h1 ci, hset]
  rw [he] at hs
  have hLk : ∀ a ∈ L, lt a.2 k := by
    rcases hL with rfl | ⟨L', a, j, rfl, hj, ha⟩
    · simp
    · have hak := hlo j a hj ha
      have hs' : Sorted lt (L' ++ a :: (ci.elems ++ R)) := by simpa using hs
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact ho.trans _ _ _ ((sorted_mid hs').1 x hx) hak
      · simp at hx; subst hx; exact hak
  have hRk : ∀ b ∈ R, lt k b.2 := by
    rcases hR with rfl | ⟨R', b, j, rfl, hj, hb⟩
    · simp
    · have hbk := hhi j b hj hb
      have hs' : Sorted lt ((L ++ ci.elems) ++ b :: R') := hs
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hbk
      · exact ho.trans _ _ _ hbk ((sorted_mid hs').2 x hx)
  refine ⟨sorted_sublist ((List.sublist_append_right L _).trans
      (List.sublist_append_left _ R)) hs, fun x hx => by rw [he]; simp [hx], ?_, ?_⟩
  · rw [he, lookup_app_right _ _ _ (fun b hb => (ho.ins_ne (hRk b hb)).symm),
      lookup_app_left _ _ _ (fun a ha => ho.ins_ne (hLk a ha))]
  · intro c' v hc'
    rw [h1 c', hc', he, insert_mid ho L _ R (v, k) hLk hRk]

/-- Replacing item `i`, which has the key. -/
theorem found_item (ho : StrictOrder lt) (is : List (V × K)) (cs : List (Tree (V × K)))
    (i : Nat) (x : V × K) (k : K) (hx : is[i]? = some x) (hk : x.2 = k)
    (hs : Sorted lt (elemsAux is cs)) :
    lookup (elemsAux is cs) k = some x.1 ∧
      ∀ v : V, elemsAux (is.set i (v, k)) cs = insert lt (elemsAux is cs) (v, k) := by
  obtain ⟨A, B, h1, h2⟩ := elemsAux_item is cs i x hx
  rw [h1] at hs ⊢
  have hA := (sorted_mid hs).1
  rw [hk] at hA
  refine ⟨?_, fun v => ?_⟩
  · rw [lookup_app_left _ _ _ (fun a ha => ho.ins_ne (hA a ha)), lookup_cons_eq _ _ _ hk]
  · rw [h2, insert_replace ho A B x (v, k) hA hk]

/-- Inserting into a leaf at `countLt`. -/
theorem leaf_insert (ho : StrictOrder lt) (is : List (V × K)) (i : Nat) (k : K)
    (hlo : ∀ j a, j < i → is[j]? = some a → lt a.2 k)
    (hhi : ∀ j a, i ≤ j → is[j]? = some a → lt k a.2) :
    lookup is k = none ∧ ∀ v : V, is.take i ++ (v, k) :: is.drop i = insert lt is (v, k) := by
  have hA : ∀ a ∈ is.take i, lt a.2 k := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.1 ha
    exact hlo j _ (by omega) (List.getElem?_eq_getElem _)
  have hB : ∀ b ∈ is.drop i, lt k b.2 := by
    intro b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.1 hb
    exact hhi (i + j) _ (by omega) (List.getElem?_eq_getElem _)
  refine ⟨?_, fun v => ?_⟩
  · rw [← List.take_append_drop i is]
    apply lookup_none
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact ho.ins_ne (hA a ha)
    · exact (ho.ins_ne (hB a ha)).symm
  · conv => rhs; rw [← List.take_append_drop i is]
    rw [insert_split ho _ _ (v, k) hA hB]

theorem getElem?_insertAt {A : Type} (is : List A) (e : A) (i j : Nat) (hi : i ≤ is.length) :
    (is.take i ++ e :: is.drop i)[j]? =
      if j < i then is[j]? else if j = i then some e else is[j - 1]? := by
  have ht : (is.take i).length = i := by simp; omega
  by_cases h1 : j < i
  · rw [ifP h1, List.getElem?_append_left (by omega), List.getElem?_take, ifP h1]
  · rw [ifN h1, List.getElem?_append_right (by omega), ht]
    by_cases h2 : j = i
    · subst h2; simp
    · rw [ifN h2]
      obtain ⟨m, hm⟩ : ∃ m, j - i = m + 1 := ⟨j - i - 1, by omega⟩
      rw [hm, List.getElem?_cons_succ, List.getElem?_drop]
      congr 1; omega

theorem getElem?_split_left {A : Type} (cs : List A) (i : Nat) (L R : A) (hi : i < cs.length) :
    (cs.take i ++ L :: R :: cs.drop (i + 1))[i]? = some L := by
  rw [List.getElem?_append_right (by simp; omega)]
  have : i - (cs.take i).length = 0 := by simp; omega
  rw [this]; rfl

theorem getElem?_split_right {A : Type} (cs : List A) (i : Nat) (L R : A) (hi : i < cs.length) :
    (cs.take i ++ L :: R :: cs.drop (i + 1))[i + 1]? = some R := by
  rw [List.getElem?_append_right (by simp; omega)]
  have : i + 1 - (cs.take i).length = 1 := by simp; omega
  rw [this]; rfl

/-- After the split, `k` below the item that moved up: child `i`. -/
theorem split_bounds_left (is : List (V × K)) (i : Nat) (e : V × K) (k : K) (hi : i ≤ is.length)
    (hlo : ∀ j a, j < i → is[j]? = some a → lt a.2 k)
    (hhi : ∀ j a, i ≤ j → is[j]? = some a → lt k a.2) (hk : lt k e.2) :
    (∀ j a, j < i → (is.take i ++ e :: is.drop i)[j]? = some a → lt a.2 k) ∧
    (∀ j a, i ≤ j → (is.take i ++ e :: is.drop i)[j]? = some a → lt k a.2) := by
  constructor
  · intro j a hj ha
    rw [getElem?_insertAt _ _ _ _ hi, ifP hj] at ha
    exact hlo j a hj ha
  · intro j a hj ha
    rw [getElem?_insertAt _ _ _ _ hi, ifN (by omega)] at ha
    by_cases h : j = i
    · rw [ifP h] at ha; cases ha; exact hk
    · rw [ifN h] at ha; exact hhi _ a (by omega) ha

/-- After the split, `k` above the item that moved up: child `i + 1`. -/
theorem split_bounds_right (is : List (V × K)) (i : Nat) (e : V × K) (k : K) (hi : i ≤ is.length)
    (hlo : ∀ j a, j < i → is[j]? = some a → lt a.2 k)
    (hhi : ∀ j a, i ≤ j → is[j]? = some a → lt k a.2) (hk : lt e.2 k) :
    (∀ j a, j < i + 1 → (is.take i ++ e :: is.drop i)[j]? = some a → lt a.2 k) ∧
    (∀ j a, i + 1 ≤ j → (is.take i ++ e :: is.drop i)[j]? = some a → lt k a.2) := by
  constructor
  · intro j a hj ha
    rw [getElem?_insertAt _ _ _ _ hi] at ha
    by_cases h1 : j < i
    · rw [ifP h1] at ha; exact hlo j a h1 ha
    · rw [ifN h1, ifP (by omega)] at ha; cases ha; exact hk
  · intro j a hj ha
    rw [getElem?_insertAt _ _ _ _ hi, ifN (by omega), ifN (by omega)] at ha
    exact hhi _ a (by omega) ha

/-! ### `insert` keeps the list sorted -/

theorem model_mem_insert (s : List (V × K)) (e x : V × K) (h : x ∈ insert lt s e) : x ∈ s ∨ x = e := by
  induction s with
  | nil => simp [insert] at h; exact .inr h
  | cons y s ih =>
    unfold insert at h
    by_cases h1 : lt e.2 y.2
    · rw [ifP h1] at h
      rcases List.mem_cons.1 h with h | h
      · exact .inr h
      · exact .inl h
    · rw [ifN h1] at h
      by_cases h2 : e.2 = y.2
      · rw [ifP h2] at h
        rcases List.mem_cons.1 h with h | h
        · exact .inr h
        · exact .inl (List.mem_cons_of_mem _ h)
      · rw [ifN h2] at h
        rcases List.mem_cons.1 h with h | h
        · exact .inl (by simp [h])
        · rcases ih h with h | h
          · exact .inl (List.mem_cons_of_mem _ h)
          · exact .inr h

theorem model_sorted_insert (ho : StrictOrder lt) (s : List (V × K)) (e : V × K) (hs : Sorted lt s) :
    Sorted lt (insert lt s e) := by
  induction s with
  | nil => simp [insert, Sorted]
  | cons y s ih =>
    unfold Sorted at hs
    rw [List.pairwise_cons] at hs
    unfold insert
    by_cases h1 : lt e.2 y.2
    · rw [ifP h1]
      unfold Sorted
      rw [List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, hs.1, hs.2⟩
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact h1
      · exact ho.trans _ _ _ h1 (hs.1 b hb)
    · rw [ifN h1]
      by_cases h2 : e.2 = y.2
      · rw [ifP h2]
        unfold Sorted
        rw [List.pairwise_cons]
        exact ⟨fun b hb => h2 ▸ hs.1 b hb, hs.2⟩
      · rw [ifN h2]
        have hy : lt y.2 e.2 := by
          rcases ho.total e.2 y.2 with h | h | h
          · exact absurd h h1
          · exact absurd h h2
          · exact h
        unfold Sorted
        rw [List.pairwise_cons]
        refine ⟨fun b hb => ?_, ih hs.2⟩
        rcases model_mem_insert s e b hb with hb | rfl
        · exact hs.1 b hb
        · exact hy

theorem model_length_insert (ho : StrictOrder lt) (s : List (V × K)) (e : V × K) (hs : Sorted lt s) :
    (insert lt s e).length = s.length + (if (lookup s e.2).isSome then 0 else 1) := by
  induction s with
  | nil => simp [insert, lookup]
  | cons y s ih =>
    unfold Sorted at hs
    rw [List.pairwise_cons] at hs
    unfold insert
    by_cases h1 : lt e.2 y.2
    · rw [ifP h1]
      have : lookup (y :: s) e.2 = none := by
        apply lookup_none
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact (ho.ins_ne h1).symm
        · exact (ho.ins_ne (ho.trans _ _ _ h1 (hs.1 a ha))).symm
      simp [this]
    · rw [ifN h1]
      by_cases h2 : e.2 = y.2
      · rw [ifP h2, lookup_cons_eq _ _ _ h2.symm]
        simp
      · rw [ifN h2]
        have : lookup (y :: s) e.2 = lookup s e.2 :=
          lookup_app_left [y] s e.2 (by simp; exact fun h => h2 h.symm)
        rw [this, List.length_cons, List.length_cons, ih hs.2]
        omega

end insert

section shape
variable {E : Type}

theorem shape_zero (d : Nat) (is : List E) (cs : List (Tree E)) :
    Shape d 0 (.node is cs) ↔ cs = [] := by rw [Shape]

theorem shape_succ (d h : Nat) (is : List E) (cs : List (Tree E)) :
    Shape d (h + 1) (.node is cs) ↔ cs.length = is.length + 1 ∧
      ∀ c ∈ cs, (d - 1 ≤ c.items.length ∧ c.items.length ≤ 2 * d - 1) ∧ Shape d h c := by
  rw [Shape]

theorem shape_children (d h : Nat) (is : List E) (cs : List (Tree E))
    (hs : Shape d h (.node is cs)) : cs = [] ∨ cs.length = is.length + 1 := by
  cases h with
  | zero => exact .inl ((shape_zero d is cs).1 hs)
  | succ h => exact .inr ((shape_succ d h is cs).1 hs).1

theorem shape_set_items (d h : Nat) (is is' : List E) (cs : List (Tree E))
    (hl : is'.length = is.length) (hs : Shape d h (.node is cs)) : Shape d h (.node is' cs) := by
  cases h with
  | zero => exact (shape_zero d is' cs).2 ((shape_zero d is cs).1 hs)
  | succ h =>
    rw [shape_succ] at hs ⊢
    exact ⟨hl ▸ hs.1, hs.2⟩

theorem shape_child (d h : Nat) (is : List E) (cs : List (Tree E)) (i : Nat) (ci : Tree E)
    (hs : Shape d (h + 1) (.node is cs)) (hci : cs[i]? = some ci) :
    (d - 1 ≤ ci.items.length ∧ ci.items.length ≤ 2 * d - 1) ∧ Shape d h ci :=
  ((shape_succ d h is cs).1 hs).2 ci (List.mem_of_getElem? hci)

theorem shape_set_child (d h : Nat) (is : List E) (cs : List (Tree E)) (i : Nat) (t : Tree E)
    (hs : Shape d (h + 1) (.node is cs)) (ht : Shape d h t)
    (hb : d - 1 ≤ t.items.length ∧ t.items.length ≤ 2 * d - 1) :
    Shape d (h + 1) (.node is (cs.set i t)) := by
  rw [shape_succ] at hs ⊢
  refine ⟨by simp [hs.1], fun c hc => ?_⟩
  rcases List.mem_or_eq_of_mem_set hc with hc | rfl
  · exact hs.2 c hc
  · exact ⟨hb, ht⟩

/-- The two halves of a full node split at `d - 1`. -/
theorem shape_halves (d h : Nat) (cis : List E) (ccs : List (Tree E)) (m : Nat)
    (hd : 1 ≤ d) (hm : m = d - 1) (hlen : cis.length = 2 * d - 1)
    (hs : Shape d h (.node cis ccs)) :
    (Shape d h (.node (cis.take m) (ccs.take (m + 1))) ∧ (cis.take m).length = d - 1) ∧
    (Shape d h (.node (cis.drop (m + 1)) (ccs.drop (m + 1))) ∧
      (cis.drop (m + 1)).length = d - 1) := by
  subst hm
  refine ⟨⟨?_, by simp; omega⟩, ⟨?_, by simp; omega⟩⟩
  · cases h with
    | zero => rw [shape_zero] at hs ⊢; simp [hs]
    | succ h =>
      rw [shape_succ] at hs ⊢
      exact ⟨by simp; omega, fun c hc => hs.2 c (List.mem_of_mem_take hc)⟩
  · cases h with
    | zero => rw [shape_zero] at hs ⊢; simp [hs]
    | succ h =>
      rw [shape_succ] at hs ⊢
      exact ⟨by simp; omega, fun c hc => hs.2 c (List.mem_of_mem_drop hc)⟩

/-- Splitting a full child `i` of a node at `d - 1`. -/
theorem shape_splitChild (d h : Nat) (is : List E) (cs : List (Tree E)) (i m : Nat)
    (cis : List E) (ccs : List (Tree E)) (e : E) (hd : 1 ≤ d) (hm : m = d - 1)
    (hs : Shape d (h + 1) (.node is cs)) (hci : cs[i]? = some (.node cis ccs))
    (hlen : cis.length = 2 * d - 1) :
    Shape d (h + 1) (.node (is.take i ++ e :: is.drop i)
      (cs.take i ++ .node (cis.take m) (ccs.take (m + 1)) ::
        .node (cis.drop (m + 1)) (ccs.drop (m + 1)) :: cs.drop (i + 1))) := by
  have hi : i < cs.length := by
    rcases List.getElem?_eq_some_iff.1 hci with ⟨h, _⟩; exact h
  have ⟨_, hcs⟩ := shape_child d h is cs i _ hs hci
  obtain ⟨⟨hL, hLl⟩, ⟨hR, hRl⟩⟩ := shape_halves d h cis ccs m hd hm hlen hcs
  rw [shape_succ] at hs ⊢
  refine ⟨by simp; omega, fun c hc => ?_⟩
  simp only [List.mem_append, List.mem_cons] at hc
  rcases hc with hc | rfl | rfl | hc
  · exact hs.2 c (List.mem_of_mem_take hc)
  · exact ⟨by simp only [items_node]; omega, hL⟩
  · exact ⟨by simp only [items_node]; omega, hR⟩
  · exact hs.2 c (List.mem_of_mem_drop hc)

end shape

section iris
open Iris Iris.BI Iris.ProofMode
variable {GF : BundledGFunctors} {V K : Type}

theorem allItems_mono (o : ItemOrder GF V K) (l l' : List (V × K)) (h : ∀ x ∈ l, x ∈ l') :
    allItems o l' ⊢ allItems o l := by
  unfold allItems
  iintro #H
  imodintro
  iintro %e %he
  iapply H $$ %e %(h e he)

theorem allItems_mem (o : ItemOrder GF V K) (l : List (V × K)) (x : V × K) (h : x ∈ l) :
    allItems o l ⊢ o.item x.1 x.2 := by
  unfold allItems
  iintro #H
  iapply H $$ %x %h

end iris

section iris2
open Iris Iris.BI Iris.ProofMode
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {K : Type}

theorem ownNode_ne_null
    (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (dq : DFrac) (n : Loc)
    (t : Tree (V × K)) : ownNode o c f less dq n t ⊢ ⌜n ≠ null⌝ := by
  obtain ⟨is, cs⟩ := t
  rw [ownNode_node]
  unfold ownedNode nodeShallow nodeFields
  rw [frozen_node]
  unfold nodeFields
  iintro (⟨%ps, ⟨%isl, %csl, ⟨%Hnn, _⟩, _⟩, _⟩ | ⟨%isl, %csl, %cow, %ps, ⟨%Hnn, _⟩, _⟩)
  · ipureintro; exact Hnn
  · ipureintro; exact Hnn

end iris2

end InsertLemmas
end Btree
end EtcdGrove
end Perennial
