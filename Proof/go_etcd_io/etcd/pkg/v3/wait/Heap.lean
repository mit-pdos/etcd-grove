/-
The pure model of `pkg/wait`'s `deadlineHeap` (`wait_time.go`, etcd PR #22495): a binary min-heap
of `uint64` deadlines in a list, `heapOk`, and the invariants of its two loops, `push`'s sift-up
(`siftUpInv`) and `pop`'s sift-down (`siftDownInv`), with their steps. Lean-first (no Rocq
counterpart; pr-verify/etcd-22495, 2026-10-17).

The heap order is on the deadlines as unsigned integers (`uint.Z`), as Go compares `uint64`s.
Node `j > 0`'s parent is `(j - 1) / 2`; node `i`'s children are `2i + 1` and `2i + 2`.

Both loop invariants say the heap order holds on every parent-child edge but those at one node
`i` (sift-up: the edge from `i` to its parent; sift-down: the edges from `i` to its children), and
bridge the gap: `i`'s parent is at most each of `i`'s children.
-/
module

public import Perennial.Std.List
public import Perennial.Std.Word

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace waitHeap

/-- **`xs` is a min-heap** (of `uint64`s): every node is at least its parent. -/
def heapOk (xs : List w64) : Prop :=
  ∀ (j : Nat) (a b : w64), 0 < j → xs[(j - 1) / 2]? = some a → xs[j]? = some b →
    uint.Z a ≤ uint.Z b

/-- **The sift-up invariant at `i`**: the heap order on every edge but `i`'s to its parent, and
`i`'s parent at most `i`'s children. -/
def siftUpInv (xs : List w64) (i : Nat) : Prop :=
  (∀ (j : Nat) (a b : w64), 0 < j → j ≠ i → xs[(j - 1) / 2]? = some a → xs[j]? = some b →
    uint.Z a ≤ uint.Z b) ∧
  (0 < i → ∀ (j : Nat) (a b : w64), 0 < j → (j - 1) / 2 = i → xs[(i - 1) / 2]? = some a →
    xs[j]? = some b → uint.Z a ≤ uint.Z b)

/-- **The sift-down invariant at `i`**: the heap order on every edge but `i`'s to its children,
and `i`'s parent at most `i`'s children. -/
def siftDownInv (xs : List w64) (i : Nat) : Prop :=
  (∀ (j : Nat) (a b : w64), 0 < j → (j - 1) / 2 ≠ i → xs[(j - 1) / 2]? = some a →
    xs[j]? = some b → uint.Z a ≤ uint.Z b) ∧
  (0 < i → ∀ (j : Nat) (a b : w64), 0 < j → (j - 1) / 2 = i → xs[(i - 1) / 2]? = some a →
    xs[j]? = some b → uint.Z a ≤ uint.Z b)

/-- **`c` is the least child of `i`**, holding `vc`. -/
def minChild (xs : List w64) (i c : Nat) (vc : w64) : Prop :=
  (c = 2 * i + 1 ∨ c = 2 * i + 2) ∧ xs[c]? = some vc ∧
  ∀ (j : Nat) (v : w64), 0 < j → (j - 1) / 2 = i → xs[j]? = some v → uint.Z vc ≤ uint.Z v

theorem lookup_lt {xs : List α} {i : Nat} {x : α} (h : xs[i]? = some x) : i < xs.length :=
  (List.getElem?_eq_some_iff.1 h).1

theorem lookup_some {xs : List α} {i : Nat} (h : i < xs.length) : ∃ x, xs[i]? = some x :=
  ⟨_, List.getElem?_eq_getElem h⟩

/-- A swap's lookups. -/
theorem swap_lookup' (xs : List α) (i j k : Nat) (a b : α) (hi : i < xs.length)
    (hj : j < xs.length) :
    ((xs.set j b).set i a)[k]? = if k = i then some a else if k = j then some b else xs[k]? := by
  rw [List.getElem?_set]
  by_cases hki : k = i
  · subst hki; simp [hi]
  · rw [ite_eq_right (Ne.symm hki), ite_eq_right hki, List.getElem?_set]
    by_cases hkj : k = j
    · subst hkj; simp [hj]
    · rw [ite_eq_right (Ne.symm hkj), ite_eq_right hkj]

/-- A swap is a permutation. -/
theorem swap_perm (xs : List α) (i j : Nat) (a b : α) (ha : xs[j]? = some a)
    (hb : xs[i]? = some b) : (xs.set j b).set i a ≡ₚ xs :=
  Permutation_insert_swap xs j i a b ha hb

/-- **A heap's root is its least element.** -/
theorem heapOk_root_le {xs : List w64} (h : heapOk xs) {m : w64} (hm : xs[0]? = some m) :
    ∀ (j : Nat) (x : w64), xs[j]? = some x → uint.Z m ≤ uint.Z x := by
  suffices H : ∀ (n j : Nat) (x : w64), j < n → xs[j]? = some x → uint.Z m ≤ uint.Z x from
    fun j x hx => H (j + 1) j x (Nat.lt_succ_self j) hx
  intro n
  induction n with
  | zero => intro j x hj; omega
  | succ n ih' =>
    intro j x hjn hx
    have ih : ∀ k, k < j → ∀ y, xs[k]? = some y → uint.Z m ≤ uint.Z y :=
      fun k hk y hy => ih' k y (by omega) hy
    by_cases hj : j = 0
    · subst hj; rw [hm] at hx; cases hx; exact Int.le_refl _
    · have hlt := lookup_lt hx
      obtain ⟨a, ha⟩ := lookup_some (xs := xs) (i := (j - 1) / 2) (by omega)
      exact Int.le_trans (ih _ (by omega) a ha) (h j a x (by omega) ha hx)

theorem heapOk_min {xs : List w64} (h : heapOk xs) {m : w64} (hm : xs[0]? = some m) :
    ∀ x ∈ xs, uint.Z m ≤ uint.Z x := by
  intro x hx
  obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
  exact heapOk_root_le h hm j x (by rw [List.getElem?_eq_getElem hj, hjx])

theorem heapOk_nil : heapOk ([] : List w64) := by
  intro j a b _ _ hb; simp at hb

/-! ### `push`'s sift-up -/

/-- The sift-up starts at the appended element. -/
theorem siftUp_init {xs : List w64} (h : heapOk xs) (d : w64) :
    siftUpInv (xs ++ [d]) xs.length := by
  constructor
  · intro j a b hj hjn ha hb
    have hjl := lookup_lt hb
    simp only [List.length_append, List.length_singleton] at hjl
    rw [List.getElem?_append_left (by omega)] at ha hb
    exact h j a b hj ha hb
  · intro _ j a b hj hji _ hb
    have hjl := lookup_lt hb
    simp only [List.length_append, List.length_singleton] at hjl
    omega

/-- The sift-up ends at the root. -/
theorem siftUp_done_root {xs : List w64} (h : siftUpInv xs 0) : heapOk xs :=
  fun j a b hj ha hb => h.1 j a b hj (by omega) ha hb

/-- The sift-up ends where the node is at least its parent. -/
theorem siftUp_done_le {xs : List w64} {i : Nat} (h : siftUpInv xs i) {a b : w64}
    (ha : xs[(i - 1) / 2]? = some a) (hb : xs[i]? = some b) (hab : uint.Z a ≤ uint.Z b) :
    heapOk xs := by
  intro j a' b' hj ha' hb'
  by_cases hji : j = i
  · subst hji; rw [ha] at ha'; rw [hb] at hb'; cases ha'; cases hb'; exact hab
  · exact h.1 j a' b' hj hji ha' hb'

/-- One sift-up step: a node `i` less than its parent `p` swaps with it. -/
theorem siftUp_step {xs : List w64} {i : Nat} (h : siftUpInv xs i) (hi : 0 < i) {a b : w64}
    (ha : xs[(i - 1) / 2]? = some a) (hb : xs[i]? = some b) (hlt : uint.Z b < uint.Z a) :
    siftUpInv ((xs.set ((i - 1) / 2) b).set i a) ((i - 1) / 2) := by
  have hil := lookup_lt hb
  have hpl := lookup_lt ha
  have hpi : (i - 1) / 2 ≠ i := by omega
  have L := fun k => swap_lookup' xs i ((i - 1) / 2) k a b hil hpl
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro j a' b' hj hjp ha' hb'
    rw [L] at ha' hb'
    by_cases hji : j = i
    · -- the edge `(p, i)`: now `b` above `a`
      subst hji
      simp only [ite_eq_right hpi, ite_eq_left rfl] at ha'
      simp only [ite_eq_left rfl] at hb'
      cases ha'; cases hb'; exact Int.le_of_lt hlt
    · simp only [ite_eq_right hji, ite_eq_right hjp] at hb'
      by_cases hqi : (j - 1) / 2 = i
      · -- a child of `i`: under `a`, the old parent, by the bridge
        simp only [ite_eq_left hqi] at ha'
        rw [← (Option.some.inj ha')]
        exact h2 hi j a b' hj hqi ha hb'
      · by_cases hqp : (j - 1) / 2 = (i - 1) / 2
        · -- a sibling of `i`: under `b < a ≤` it
          simp only [ite_eq_right hqi, ite_eq_left hqp] at ha'
          cases ha'
          rw [← hqp] at ha
          exact Int.le_trans (Int.le_of_lt hlt) (h1 j a b' hj hji ha hb')
        · simp only [ite_eq_right hqi, ite_eq_right hqp] at ha'
          exact h1 j a' b' hj hji ha' hb'
  · intro hp0 j a' b' hj hjq ha' hb'
    rw [L] at ha' hb'
    have hpp1 : ((i - 1) / 2 - 1) / 2 ≠ i := by omega
    have hpp2 : ((i - 1) / 2 - 1) / 2 ≠ (i - 1) / 2 := by omega
    simp only [ite_eq_right hpp1, ite_eq_right hpp2] at ha'
    -- `a'` is the grandparent of `i`, at most `a` (the edge `(pp, p)`, `p ≠ i`)
    have hpa : uint.Z a' ≤ uint.Z a := h1 ((i - 1) / 2) a' a (by omega) hpi ha' ha
    by_cases hji : j = i
    · subst hji; simp only [ite_eq_left rfl] at hb'; cases hb'; exact hpa
    · have hjp : j ≠ (i - 1) / 2 := by omega
      simp only [ite_eq_right hji, ite_eq_right hjp] at hb'
      -- another child of `p`, at least `a`
      have : uint.Z a ≤ uint.Z b' := by
        rw [← hjq] at ha; exact h1 j a b' hj hji ha hb'
      exact Int.le_trans hpa this

/-! ### `pop`'s sift-down -/

/-- After `pop` moved the last element to the root and dropped the last slot, the sift-down
starts at the root. -/
theorem siftDown_init {xs : List w64} (h : heapOk xs) {n : Nat} (hn : xs.length = n + 1)
    {z : w64} (_hz : xs[n]? = some z) : siftDownInv ((xs.set 0 z).take n) 0 := by
  constructor
  · intro j a b hj hq ha hb
    rw [List.getElem?_take] at ha hb
    have hjn : j < n := by
      by_cases hjn : j < n
      · exact hjn
      · simp [hjn] at hb
    simp only [show (j - 1) / 2 < n by omega, if_true, hjn, List.getElem?_set] at ha hb
    simp only [show ¬ (0 = j) by omega, if_false] at hb
    simp only [show ¬ (0 = (j - 1) / 2) by omega, if_false] at ha
    exact h j a b hj ha hb
  · intro h0; omega

/-- The sift-down ends at a node with no children. -/
theorem siftDown_done_leaf {xs : List w64} {i : Nat} (h : siftDownInv xs i)
    (hn : xs.length ≤ 2 * i + 1) : heapOk xs := by
  intro j a b hj ha hb
  by_cases hq : (j - 1) / 2 = i
  · have := lookup_lt hb; omega
  · exact h.1 j a b hj hq ha hb

/-- The sift-down ends at a node at most its least child. -/
theorem siftDown_done_le {xs : List w64} {i c : Nat} {vc vi : w64} (h : siftDownInv xs i)
    (hc : minChild xs i c vc) (hi : xs[i]? = some vi) (hle : uint.Z vi ≤ uint.Z vc) :
    heapOk xs := by
  intro j a b hj ha hb
  by_cases hq : (j - 1) / 2 = i
  · rw [hq, hi] at ha; cases ha
    exact Int.le_trans hle (hc.2.2 j b hj hq hb)
  · exact h.1 j a b hj hq ha hb

/-- The least child, as `pop` picks it: the left one `l`, or the right one `l + 1` if it exists and
is less. -/
theorem minChild_pick {xs : List w64} {i : Nat} {vl : w64} (hl : xs[2 * i + 1]? = some vl)
    (vr : Option w64) (hr : xs[2 * i + 2]? = vr) :
    (∀ v, vr = some v → uint.Z v < uint.Z vl → minChild xs i (2 * i + 2) v) ∧
    ((∀ v, vr = some v → ¬ uint.Z v < uint.Z vl) → minChild xs i (2 * i + 1) vl) := by
  have children : ∀ j, 0 < j → (j - 1) / 2 = i → j = 2 * i + 1 ∨ j = 2 * i + 2 := by
    intro j _ h; omega
  constructor
  · intro v hv hlt
    refine ⟨Or.inr rfl, hv ▸ hr, ?_⟩
    intro j w hj hq hw
    rcases children j hj hq with rfl | rfl
    · rw [hl] at hw; cases hw; exact Int.le_of_lt hlt
    · rw [hr, hv] at hw; cases hw; exact Int.le_refl _
  · intro hnot
    refine ⟨Or.inl rfl, hl, ?_⟩
    intro j w hj hq hw
    rcases children j hj hq with rfl | rfl
    · rw [hl] at hw; cases hw; exact Int.le_refl _
    · have := hnot w (by rw [← hr, hw]); omega

/-- One sift-down step: a node `i` greater than its least child `c` swaps with it. -/
theorem siftDown_step {xs : List w64} {i c : Nat} {vc vi : w64} (h : siftDownInv xs i)
    (hc : minChild xs i c vc) (hi : xs[i]? = some vi) (hlt : uint.Z vc < uint.Z vi) :
    siftDownInv ((xs.set i vc).set c vi) c := by
  obtain ⟨hcc, hcv, hcm⟩ := hc
  have hil := lookup_lt hi
  have hcl := lookup_lt hcv
  have hci : c ≠ i := by omega
  have hpc : (c - 1) / 2 = i := by omega
  have L := fun k => swap_lookup' xs c i k vi vc hcl hil
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro j a b hj hq ha hb
    rw [L] at ha hb
    by_cases hqi : (j - 1) / 2 = i
    · -- an edge from `i`, now holding `vc`
      simp only [hqi, ite_eq_right (Ne.symm hci), ite_eq_left rfl] at ha
      cases ha
      by_cases hjc : j = c
      · subst hjc; simp only [ite_eq_left rfl] at hb; cases hb; exact Int.le_of_lt hlt
      · have hji : j ≠ i := by omega
        simp only [ite_eq_right hjc, ite_eq_right hji] at hb
        exact hcm j b hj hqi hb
    · by_cases hji : j = i
      · -- the edge into `i`, from its parent, by the bridge
        subst hji
        have hj0 : 0 < j := hj
        have hpc' : (j - 1) / 2 ≠ c := by omega
        simp only [ite_eq_right hqi, ite_eq_right hpc'] at ha
        simp only [ite_eq_right (Ne.symm hci), ite_eq_left rfl] at hb
        rw [← (Option.some.inj hb)]
        exact h2 hj0 c a vc (by omega) hpc ha hcv
      · have hjc : j ≠ c := by omega
        simp only [ite_eq_right hjc, ite_eq_right hji] at hb
        simp only [ite_eq_right hq, ite_eq_right hqi] at ha
        exact h1 j a b hj hqi ha hb
  · intro _ j a b hj hq ha hb
    rw [L] at ha hb
    rw [hpc] at ha
    simp only [ite_eq_right (Ne.symm hci), ite_eq_left rfl] at ha
    cases ha
    have hjc : j ≠ c := by omega
    have hji : j ≠ i := by omega
    simp only [ite_eq_right hjc, ite_eq_right hji] at hb
    exact h1 j vc b hj (by omega) (by rw [hq]; exact hcv) hb

/-! ### The elements -/

/-- `pop`'s list: the root's slot gets the last element, then the last slot goes; the rest of
the elements. -/
theorem pop_perm {xs : List w64} {n : Nat} (hn : xs.length = n + 1) {z : w64}
    (hz : xs[n]? = some z) {t : w64} (ht : xs[0]? = some t) :
    t :: (xs.set 0 z).take n ≡ₚ xs := by
  match xs, hn with
  | x :: rest, hn =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hn
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
    subst ht
    cases n with
    | zero =>
      have : rest = [] := List.eq_nil_of_length_eq_zero hn
      subst this; simp
    | succ n =>
      simp only [List.set_cons_zero, List.take_succ_cons]
      apply List.Perm.cons
      -- `z :: rest.take n ≡ₚ rest`, `rest = rest.take n ++ [z]`
      have hz' : rest[n]? = some z := by simpa using hz
      have hsplit : rest = rest.take n ++ [z] := by
        conv => lhs; rw [← List.take_append_drop n rest]
        congr 1
        have hd : (rest.drop n).length = 1 := by simp; omega
        match hdr : rest.drop n, hd with
        | [w], _ =>
          have h0 : (rest.drop n)[0]? = some w := by rw [hdr]; rfl
          have : rest[n]? = some w := by
            rw [List.getElem?_drop] at h0; simpa using h0
          rw [hz'] at this; cases this; rfl
      conv => rhs; rw [hsplit]
      exact List.perm_append_singleton z (rest.take n) |>.symm

end waitHeap
end EtcdGrove
end Perennial

namespace Perennial
namespace EtcdGrove
namespace waitHeap

/-! ### The heap and the map of `*timeList` -/

/-- **The heap `xs` holds exactly the map `M`'s deadlines**, once each. -/
def heapMatch {V : Type} (xs : List w64) (M : GMap w64 V) : Prop :=
  xs.Nodup ∧ ∀ k, k ∈ xs ↔ (M.lookup k).isSome

theorem heapMatch_empty {V : Type} : heapMatch ([] : List w64) (GMap.empty : GMap w64 V) := by
  refine ⟨List.nodup_nil, fun k => ?_⟩
  simp [GMap.empty, GMap.lookup]

theorem heapMatch_insert {V : Type} {xs xs' : List w64} {M : GMap w64 V} {d : w64} {v : V}
    (h : heapMatch xs M) (hd : M.lookup d = none) (hp : xs' ≡ₚ xs ++ [d]) :
    heapMatch xs' (GMap.insert d v M) := by
  obtain ⟨hnd, hm⟩ := h
  have hdx : d ∉ xs := fun hx => by have := (hm d).1 hx; rw [hd] at this; simp at this
  refine ⟨hp.nodup_iff.2 ?_, fun k => ?_⟩
  · rw [List.nodup_append]
    refine ⟨hnd, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; intro e; subst e; exact hdx ha
  · rw [hp.mem_iff, List.mem_append, List.mem_singleton]
    by_cases hk : k = d
    · subst hk; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), ← hm k]; simp [hk]

theorem heapMatch_delete {V : Type} {xs xs' : List w64} {M : GMap w64 V} {t : w64}
    (h : heapMatch xs M) (hp : t :: xs' ≡ₚ xs) : heapMatch xs' (GMap.delete t M) := by
  obtain ⟨hnd, hm⟩ := h
  have hnd' : (t :: xs').Nodup := hp.nodup_iff.2 hnd
  rw [List.nodup_cons] at hnd'
  refine ⟨hnd'.2, fun k => ?_⟩
  by_cases hk : k = t
  · subst hk; simp only [GMap.lookup_delete, Option.isSome_none]
    exact ⟨fun hx => absurd hx hnd'.1, fun h => by cases h⟩
  · rw [GMap.lookup_delete_ne _ (Ne.symm hk), ← hm k, ← hp.mem_iff, List.mem_cons]
    exact ⟨Or.inr, fun h => h.resolve_left hk⟩

theorem heapMatch_lookup {V : Type} {xs : List w64} {M : GMap w64 V} {t : w64}
    (h : heapMatch xs M) (ht : t ∈ xs) : ∃ v, M.lookup t = some v := by
  have := (h.2 t).1 ht
  cases hM : M.lookup t with
  | none => rw [hM] at this; simp at this
  | some v => exact ⟨v, rfl⟩

end waitHeap
end EtcdGrove
end Perennial
