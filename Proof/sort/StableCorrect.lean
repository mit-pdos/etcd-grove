/-
What the model of `sort.Stable` (`StableModel.lean`) computes: run on a list of elements
tagged with their positions (`List.zipIdx`), `stable` leaves it sorted by the strict total
order `Tlt` (the order `lt`, ties broken by the tags), so it is `List.mergeSort`'s stable sort
(`stableM_eq_mergeSort`).

Every `Less` call Go makes compares an element with one whose tag is smaller (insertion sort:
the inserted element with the sorted prefix; `symMerge`: the right run with the left run), where
`lt` agrees with `Tlt` (`lt_iff_Tlt`): so each phase keeps "this segment is a permutation sorted
by `Tlt`".
-/
module

public import Proof.sort.StableModel
-- `List.zipIdxLE`'s body (not exposed by `Init`), to compute it in `stableM_eq_mergeSort`
import all Init.Data.List.Sort.Basic

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace stableModel

variable {α : Type}

/-- Close a goal of `if`s on index arithmetic: split them, then each case by `omega` or by the
indices being equal. -/
macro "ifs_close" : tactic =>
  `(tactic| ((repeat' split) <;> first | rfl | omega | (congr 1 <;> omega) | contradiction | (simp_all; done)))

/-! ### Permutations inside a segment -/

/-- `l'` is a permutation of `l` that leaves every position outside `[s, e)` as it was. -/
def PermIn (l l' : List α) (s e : Nat) : Prop :=
  l'.Perm l ∧ ∀ p, (p < s ∨ e ≤ p) → l'[p]? = l[p]?

theorem PermIn.refl (l : List α) (s e : Nat) : PermIn l l s e := ⟨List.Perm.refl _, fun _ _ => rfl⟩

theorem PermIn.trans {l1 l2 l3 : List α} {s e : Nat} (h1 : PermIn l1 l2 s e)
    (h2 : PermIn l2 l3 s e) : PermIn l1 l3 s e :=
  ⟨h2.1.trans h1.1, fun p hp => (h2.2 p hp).trans (h1.2 p hp)⟩

theorem PermIn.mono {l l' : List α} {s e s' e' : Nat} (h : PermIn l l' s e) (hs : s' ≤ s)
    (he : e ≤ e') : PermIn l l' s' e' :=
  ⟨h.1, fun p hp => h.2 p (by omega)⟩

theorem PermIn.length {l l' : List α} {s e : Nat} (h : PermIn l l' s e) :
    l'.length = l.length := h.1.length_eq

theorem permIn_swapL (l : List α) (i j s e : Nat) (hi : s ≤ i ∧ i < e) (hj : s ≤ j ∧ j < e)
    (hil : i < l.length) (hjl : j < l.length) : PermIn l (swapL l i j) s e := by
  refine ⟨swapL_perm l i j, fun p hp => ?_⟩
  rw [swapL_getElem? l i j p hil hjl]
  ifs_close

/-- The elements of `[s, e)` after a `PermIn` were there before. -/
theorem PermIn.segFrom {l l' : List α} {s e : Nat} (h : PermIn l l' s e) (hse : s ≤ e)
    (_he : e ≤ l.length) {p : Nat} {x : α} (hp : s ≤ p ∧ p < e) (hx : l'[p]? = some x) :
    ∃ q, s ≤ q ∧ q < e ∧ l[q]? = some x := by
  have hlen := h.length
  have split : ∀ (k : List α), k.length = l.length →
      k = k.take s ++ ((k.drop s).take (e - s) ++ k.drop e) := by
    intro k _
    conv => lhs; rw [← List.take_append_drop s k]
    congr 1
    conv => lhs; rw [← List.take_append_drop (e - s) (k.drop s)]
    rw [List.drop_drop]; congr 2; omega
  have htake : l'.take s = l.take s := by
    apply List.ext_getElem?; intro i
    rw [List.getElem?_take, List.getElem?_take]
    split
    · exact h.2 i (by omega)
    · rfl
  have hdrop : l'.drop e = l.drop e := by
    apply List.ext_getElem?; intro i
    rw [List.getElem?_drop, List.getElem?_drop]
    exact h.2 _ (by omega)
  have hperm := h.1
  rw [split l' hlen, split l rfl, htake, hdrop] at hperm
  have hmid := (List.perm_append_left_iff _).1 hperm
  have hmid' := (List.perm_append_right_iff _).1 hmid
  have hxmem : x ∈ (l'.drop s).take (e - s) := by
    rw [List.mem_iff_getElem?]
    refine ⟨p - s, ?_⟩
    rw [List.getElem?_take, if_pos (show p - s < e - s by omega), List.getElem?_drop]
    rw [show s + (p - s) = p by omega]; exact hx
  have hxmem' := hmid'.subset hxmem
  rw [List.mem_iff_getElem?] at hxmem'
  obtain ⟨i, hi⟩ := hxmem'
  rw [List.getElem?_take] at hi
  split at hi
  · rw [List.getElem?_drop] at hi
    exact ⟨s + i, by omega, by omega, hi⟩
  · cases hi

/-! ### The swaps of `swapRange`, `rotate` and `symMerge`'s insertions -/

theorem swapRangeM_getElem? (l : List α) (a b k : Nat) (hab : a + k ≤ b)
    (hb : b + k ≤ l.length) (p : Nat) :
    (swapRangeM l a b k)[p]? =
      if a ≤ p ∧ p < a + k then l[p - a + b]?
      else if b ≤ p ∧ p < b + k then l[p - b + a]? else l[p]? := by
  induction k generalizing p with
  | zero => simp only [swapRangeM]; ifs_close
  | succ k ih =>
    simp only [swapRangeM]
    rw [swapL_getElem? _ _ _ _ (by rw [swapRangeM_length]; omega)
      (by rw [swapRangeM_length]; omega)]
    rw [ih (by omega) (by omega), ih (by omega) (by omega), ih (by omega) (by omega)]
    ifs_close

theorem swapRangeM_permIn (l : List α) (a b k : Nat) (hab : a ≤ b)
    (hb : b + k ≤ l.length) : PermIn l (swapRangeM l a b k) a (b + k) := by
  induction k with
  | zero => exact PermIn.refl _ _ _
  | succ k ih =>
    refine (ih (by omega)).mono (Nat.le_refl _) (by omega) |>.trans ?_
    exact permIn_swapL _ _ _ _ _ (by omega) (by omega) (by rw [swapRangeM_length]; omega)
      (by rw [swapRangeM_length]; omega)

/-- `rotate`'s loop at `i`, `j` exchanges the blocks `[m - i, m)` and `[m, m + j)`. -/
theorem rotLoop_spec (l : List α) (m i j : Nat) (hi : i ≤ m) (hj : m + j ≤ l.length) :
    PermIn l (rotLoop l m i j) (m - i) (m + j) ∧ ∀ p, (rotLoop l m i j)[p]? =
      if m - i ≤ p ∧ p < m - i + j then l[p + i]?
      else if m - i + j ≤ p ∧ p < m + j then l[p - j]? else l[p]? := by
  induction h : i + j using Nat.strongRecOn generalizing l i j with
  | _ n ih =>
  unfold rotLoop
  by_cases h0 : i = 0 ∨ j = 0
  · rw [dif_pos h0]
    refine ⟨PermIn.refl _ _ _, fun p => ?_⟩
    rcases h0 with h0 | h0 <;> subst h0 <;> ifs_close
  rw [dif_neg h0]
  by_cases hij : i = j
  · rw [if_pos hij]
    subst hij
    refine ⟨(swapRangeM_permIn l (m - i) m i (by omega) hj).mono (Nat.le_refl _) (Nat.le_refl _),
      fun p => ?_⟩
    rw [swapRangeM_getElem? l (m - i) m i (by omega) hj]
    ifs_close
  rw [if_neg hij]
  by_cases hlt : j < i
  · rw [dif_pos hlt]
    have hl1 := swapRangeM_permIn l (m - i) m j (by omega) hj
    have hc1 := swapRangeM_getElem? l (m - i) m j (by omega) hj
    have hlen : (swapRangeM l (m - i) m j).length = l.length := swapRangeM_length ..
    obtain ⟨hp, hc⟩ := ih (i - j + j) (by omega) (swapRangeM l (m - i) m j) (i - j) j
      (by omega) (by omega) rfl
    refine ⟨(hl1.mono (Nat.le_refl _) (Nat.le_refl _)).trans (hp.mono (by omega) (Nat.le_refl _)),
      fun p => ?_⟩
    rw [hc, hc1, hc1, hc1]
    ifs_close
  · rw [dif_neg hlt]
    have hl1 := swapRangeM_permIn l (m - i) (m + j - i) i (by omega) (by omega)
    have hc1 := swapRangeM_getElem? l (m - i) (m + j - i) i (by omega) (by omega)
    have hlen : (swapRangeM l (m - i) (m + j - i) i).length = l.length := swapRangeM_length ..
    obtain ⟨hp, hc⟩ := ih (i + (j - i)) (by omega) (swapRangeM l (m - i) (m + j - i) i) i
      (j - i) (by omega) (by omega) rfl
    refine ⟨(hl1.mono (Nat.le_refl _) (by omega)).trans (hp.mono (Nat.le_refl _) (by omega)),
      fun p => ?_⟩
    rw [hc, hc1, hc1, hc1]
    ifs_close

/-- `upM` moves `l[a]` to `a + c`, the elements in between one down. -/
theorem upM_spec (l : List α) (a c : Nat) (hc : a + c < l.length) :
    PermIn l (upM l a c) a (a + c + 1) ∧ ∀ p, (upM l a c)[p]? =
      if a ≤ p ∧ p < a + c then l[p + 1]? else if p = a + c then l[a]? else l[p]? := by
  induction c with
  | zero =>
    refine ⟨PermIn.refl _ _ _, fun p => ?_⟩
    simp only [upM]; all_goals ifs_close
  | succ c ih =>
    obtain ⟨hp, hch⟩ := ih (by omega)
    refine ⟨(hp.mono (Nat.le_refl _) (by omega)).trans ?_, fun p => ?_⟩
    · exact permIn_swapL _ _ _ _ _ (by omega) (by omega) (by rw [upM_length]; omega)
        (by rw [upM_length]; omega)
    · simp only [upM]
      rw [swapL_getElem? _ _ _ _ (by rw [upM_length]; omega) (by rw [upM_length]; omega)]
      rw [hch, hch, hch]
      ifs_close

/-- `downM` moves `l[m]` to `m - c`, the elements in between one up. -/
theorem downM_spec (l : List α) (m c : Nat) (hc : c ≤ m) (hm : m < l.length) :
    PermIn l (downM l m c) (m - c) (m + 1) ∧ ∀ p, (downM l m c)[p]? =
      if m - c < p ∧ p ≤ m then l[p - 1]? else if p = m - c then l[m]? else l[p]? := by
  induction c with
  | zero =>
    refine ⟨PermIn.refl _ _ _, fun p => ?_⟩
    simp only [downM]; all_goals ifs_close
  | succ c ih =>
    obtain ⟨hp, hch⟩ := ih (by omega)
    refine ⟨(hp.mono (by omega) (Nat.le_refl _)).trans ?_, fun p => ?_⟩
    · exact permIn_swapL _ _ _ _ _ (by omega) (by omega) (by rw [downM_length]; omega)
        (by rw [downM_length]; omega)
    · simp only [downM]
      rw [swapL_getElem? _ _ _ _ (by rw [downM_length]; omega) (by rw [downM_length]; omega)]
      rw [hch, hch, hch]
      ifs_close

/-- What a binary search returns: the last `i` set (after `P (i - 1)`) and the last `j` set
(after `¬ P j`). -/
theorem bsearch_spec (P : Nat → Bool) (i j : Nat) (hij : i ≤ j) :
    i ≤ bsearch P i j ∧ bsearch P i j ≤ j ∧
      (bsearch P i j = i ∨ P (bsearch P i j - 1) = true) ∧
      (bsearch P i j = j ∨ P (bsearch P i j) = false) := by
  induction h : j - i using Nat.strongRecOn generalizing i j with
  | _ n ih =>
  unfold bsearch
  by_cases hlt : i < j
  · rw [dif_pos hlt]
    by_cases hP : P ((i + j) / 2) = true
    · rw [if_pos hP]
      obtain ⟨h1, h2, h3, h4⟩ := ih (j - ((i + j) / 2 + 1)) (by omega) ((i + j) / 2 + 1) j
        (by omega) rfl
      refine ⟨by omega, h2, ?_, h4⟩
      rcases h3 with h3 | h3
      · right; rw [h3]; simpa using hP
      · right; exact h3
    · rw [if_neg hP]
      obtain ⟨h1, h2, h3, h4⟩ := ih ((i + j) / 2 - i) (by omega) i ((i + j) / 2)
        (by omega) rfl
      refine ⟨h1, by omega, h3, ?_⟩
      rcases h4 with h4 | h4
      · right; rw [h4]; simpa using hP
      · right; exact h4
  · rw [dif_neg hlt]
    exact ⟨Nat.le_refl _, hij, Or.inl rfl, Or.inl (by omega)⟩

/-! ### The order -/

/-- `lt` is a strict weak order (Perennial's `slices.StrictWeakOrder`, on Booleans). -/
structure SWO (lt : α → α → Bool) : Prop where
  irrefl : ∀ x, lt x x = false
  trans : ∀ x y z, lt x y = true → lt y z = true → lt x z = true
  ntrans : ∀ x y z, lt x y = false → lt y z = false → lt x z = false

/-- `lt` with ties broken by `key`: a strict total order on elements of distinct keys. -/
def Tlt (lt : α → α → Bool) (key : α → Nat) (x y : α) : Prop :=
  lt x y = true ∨ (lt y x = false ∧ key x < key y)

/-- The segment `[s, e)` of `l` is sorted by `R`. -/
def SortedIn (R : α → α → Prop) (l : List α) (s e : Nat) : Prop :=
  ∀ p q x y, s ≤ p → p < q → q < e → l[p]? = some x → l[q]? = some y → R x y

section order
variable {lt : α → α → Bool} {key : α → Nat}

theorem SWO.asymm (h : SWO lt) {x y : α} (hxy : lt x y = true) : lt y x = false := by
  cases hyx : lt y x
  · rfl
  · have := h.trans x y x hxy hyx; rw [h.irrefl] at this; cases this

theorem Tlt_trans (h : SWO lt) {x y z : α} (h1 : Tlt lt key x y) (h2 : Tlt lt key y z) :
    Tlt lt key x z := by
  unfold Tlt at *
  rcases h1 with h1 | ⟨h1, k1⟩ <;> rcases h2 with h2 | ⟨h2, k2⟩
  · exact Or.inl (h.trans _ _ _ h1 h2)
  · left
    cases hxz : lt x z
    · have := h.ntrans x z y hxz h2; rw [h1] at this; cases this
    · rfl
  · left
    cases hxz : lt x z
    · have := h.ntrans y x z h1 hxz; rw [h2] at this; cases this
    · rfl
  · exact Or.inr ⟨h.ntrans z y x h2 h1, by omega⟩

/-- `x ≤ y ≤ z ≤ w` with `y < z` strict. -/
theorem Tlt_trans_le (h : SWO lt) {x y z w : α} (h1 : x = y ∨ Tlt lt key x y)
    (h2 : Tlt lt key y z) (h3 : z = w ∨ Tlt lt key z w) : Tlt lt key x w := by
  have hxz : Tlt lt key x z := by
    rcases h1 with rfl | h1
    · exact h2
    · exact Tlt_trans h h1 h2
  rcases h3 with rfl | h3
  · exact hxz
  · exact Tlt_trans h hxz h3

end order

theorem SortedIn.le {R : α → α → Prop} {l : List α} {s e : Nat} (h : SortedIn R l s e)
    {p q : Nat} {x y : α} (hp : s ≤ p) (hpq : p ≤ q) (hq : q < e) (hx : l[p]? = some x)
    (hy : l[q]? = some y) : x = y ∨ R x y := by
  by_cases hpq' : p = q
  · subst hpq'; rw [hx] at hy; cases hy; exact Or.inl rfl
  · exact Or.inr (h p q x y hp (by omega) hq hx hy)

theorem SortedIn.sub {R : α → α → Prop} {l : List α} {s e s' e' : Nat} (h : SortedIn R l s e)
    (hs : s ≤ s') (he : e' ≤ e) : SortedIn R l s' e' :=
  fun p q x y hp hpq hq hx hy => h p q x y (by omega) hpq (by omega) hx hy

theorem SortedIn.congr {R : α → α → Prop} {l l' : List α} {s e : Nat} (h : SortedIn R l s e)
    (heq : ∀ p, s ≤ p → p < e → l'[p]? = l[p]?) : SortedIn R l' s e := by
  intro p q x y hp hpq hq hx hy
  rw [heq p hp (by omega)] at hx
  rw [heq q (by omega) hq] at hy
  exact h p q x y hp hpq hq hx hy

theorem sortedIn_nil {R : α → α → Prop} (l : List α) (s e : Nat) (h : e ≤ s + 1) :
    SortedIn R l s e := fun _ _ _ _ _ _ _ _ _ => by omega

theorem sortedIn_join {R : α → α → Prop} {l : List α} {s m e : Nat} (h1 : SortedIn R l s m)
    (h2 : SortedIn R l m e)
    (h3 : ∀ p q x y, s ≤ p → p < m → m ≤ q → q < e → l[p]? = some x → l[q]? = some y → R x y) :
    SortedIn R l s e := by
  intro p q x y hp hpq hq hx hy
  by_cases hpm : p < m
  · by_cases hqm : q < m
    · exact h1 p q x y hp hpq hqm hx hy
    · exact h3 p q x y hp hpm (by omega) hq hx hy
  · exact h2 p q x y (by omega) hpq hq hx hy

theorem getElem?_some_of_lt {l : List α} {p : Nat} (h : p < l.length) : ∃ x, l[p]? = some x :=
  ⟨l[p], by simp [h]⟩

/-! ### Insertion sort -/

section ins
variable {lt : α → α → Bool} {key : α → Nat}

/-- The inner loop's exit: `x` (from `i`) stopped at `j`. -/
theorem insInner_stop (hswo : SWO lt) (S L : List α) (a i j : Nat) (x : α) (hi : i < S.length)
    (hS : SortedIn (Tlt lt key) S a i)
    (hkey : ∀ p y, a ≤ p → p < i → S[p]? = some y → key y < key x)
    (haj : a ≤ j) (hji : j ≤ i)
    (hL : ∀ p, L[p]? = if p < j ∨ i < p then S[p]? else if p = j then some x else S[p - 1]?)
    (hT : ∀ p y, j ≤ p → p < i → S[p]? = some y → Tlt lt key x y)
    (hstop : a < j → ∀ y, S[j - 1]? = some y → lt x y = false) :
    SortedIn (Tlt lt key) L a (i + 1) := by
  intro p q u v hp hpq hq hu hv
  rw [hL] at hu hv
  by_cases hpj : p < j
  · rw [if_pos (Or.inl hpj)] at hu
    by_cases hqj : q < j
    · rw [if_pos (Or.inl hqj)] at hv
      exact hS p q u v hp hpq (by omega) hu hv
    · by_cases hqj' : q = j
      · rw [if_neg (by omega), if_pos hqj'] at hv
        cases hv
        have hlen : j - 1 < S.length := by omega
        obtain ⟨y, hy⟩ := getElem?_some_of_lt hlen
        have hyx : Tlt lt key y x :=
          Or.inr ⟨hstop (by omega) y hy, hkey (j - 1) y (by omega) (by omega) hy⟩
        exact Tlt_trans_le hswo (hS.le hp (by omega) (by omega) hu hy) hyx (Or.inl rfl)
      · rw [if_neg (by omega), if_neg hqj'] at hv
        exact hS p (q - 1) u v hp (by omega) (by omega) hu hv
  · by_cases hpj' : p = j
    · rw [if_neg (by omega), if_pos hpj'] at hu
      cases hu
      rw [if_neg (by omega), if_neg (by omega)] at hv
      exact hT (q - 1) v (by omega) (by omega) hv
    · rw [if_neg (by omega), if_neg hpj'] at hu
      rw [if_neg (by omega), if_neg (by omega)] at hv
      exact hS (p - 1) (q - 1) u v (by omega) (by omega) (by omega) hu hv

theorem insInner_spec (hswo : SWO lt) (S : List α) (a i : Nat) (x : α) (hi : i < S.length)
    (_hx : S[i]? = some x) (hS : SortedIn (Tlt lt key) S a i)
    (hkey : ∀ p y, a ≤ p → p < i → S[p]? = some y → key y < key x) :
    ∀ j (L : List α), a ≤ j → j ≤ i → PermIn S L a (i + 1) →
      (∀ p, L[p]? = if p < j ∨ i < p then S[p]? else if p = j then some x else S[p - 1]?) →
      (∀ p y, j ≤ p → p < i → S[p]? = some y → Tlt lt key x y) →
      PermIn S (insInner lt a j L) a (i + 1) ∧
        SortedIn (Tlt lt key) (insInner lt a j L) a (i + 1) := by
  intro j
  induction j with
  | zero =>
    intro L haj hji hP hL hT
    rw [insInner, dif_neg (by omega)]
    exact ⟨hP, insInner_stop hswo S L a i 0 x hi hS hkey haj hji hL hT (by omega)⟩
  | succ j ih =>
    intro L haj hji hP hL hT
    have hLlen := hP.length
    have hLj1 : L[j + 1]? = some x := by rw [hL, if_neg (by omega), if_pos rfl]
    rw [insInner]
    by_cases hc : a < j + 1 ∧ lessL lt L (j + 1) (j + 1 - 1) = true
    · rw [dif_pos hc]
      obtain ⟨y, hy⟩ := getElem?_some_of_lt (show j < S.length by omega)
      have hLj : L[j]? = some y := by rw [hL, if_pos (Or.inl (by omega))]; exact hy
      have hlt : lt x y = true := by
        have := hc.2; rw [show j + 1 - 1 = j by omega, lessL_eq lt L (j + 1) j x y hLj1 hLj] at this
        exact this
      simp only [show j + 1 - 1 = j by omega]
      apply ih (swapL L (j + 1) j) (by omega) (by omega)
      · exact hP.trans (permIn_swapL L (j + 1) j a (i + 1) (by omega) (by omega) (by omega)
          (by omega))
      · intro p
        rw [swapL_getElem? L (j + 1) j p (by omega) (by omega)]
        simp only [hL]
        ifs_close
      · intro p z hjp hpi hz
        by_cases hpj : p = j
        · subst hpj; rw [hy] at hz; cases hz; exact Or.inl hlt
        · exact hT p z (by omega) hpi hz
    · rw [dif_neg hc]
      refine ⟨hP, insInner_stop hswo S L a i (j + 1) x hi hS hkey haj hji hL hT ?_⟩
      intro haj' y hy
      have hLj : L[j]? = some y := by
        rw [hL, if_pos (Or.inl (by omega))]; simpa using hy
      cases h : lt x y
      · rfl
      · exfalso; apply hc
        refine ⟨haj', ?_⟩
        rw [show j + 1 - 1 = j by omega, lessL_eq lt L (j + 1) j x y hLj1 hLj, h]

/-- The keys of `l` increase on `[a, b)` (the elements are still in their original order). -/
def KeysInc (key : α → Nat) (l : List α) (a b : Nat) : Prop :=
  ∀ p q x y, a ≤ p → p < q → q < b → l[p]? = some x → l[q]? = some y → key x < key y

theorem insOuter_spec (hswo : SWO lt) (l : List α) (a b : Nat) (hb : b ≤ l.length)
    (hinc : KeysInc key l a b) :
    ∀ i (L : List α), a < i → i ≤ b → PermIn l L a i → SortedIn (Tlt lt key) L a i →
      PermIn l (insOuter lt a b i L) a b ∧ SortedIn (Tlt lt key) (insOuter lt a b i L) a b := by
  intro i
  induction h : b - i using Nat.strongRecOn generalizing i with
  | _ n ih =>
  intro L hai hib hP hS
  rw [insOuter]
  by_cases hlt : i < b
  · rw [dif_pos hlt]
    have hLlen := hP.length
    obtain ⟨x, hx⟩ := getElem?_some_of_lt (show i < l.length by omega)
    have hLx : L[i]? = some x := by rw [hP.2 i (Or.inr (Nat.le_refl _))]; exact hx
    have hkey : ∀ p y, a ≤ p → p < i → L[p]? = some y → key y < key x := by
      intro p y hp hpi hy
      obtain ⟨q, hq1, hq2, hq⟩ := hP.segFrom (by omega) (by omega) ⟨hp, hpi⟩ hy
      exact hinc q i y x hq1 hq2 hlt hq hx
    obtain ⟨hP', hS'⟩ := insInner_spec hswo L a i x (by omega) hLx hS hkey i L (by omega)
      (Nat.le_refl _) (PermIn.refl _ _ _)
      (fun p => by ifs_close) (fun _ _ _ _ _ => by omega)
    exact ih (b - (i + 1)) (by omega) (i + 1) rfl _ (by omega) (by omega)
      ((hP.mono (Nat.le_refl _) (by omega)).trans hP') hS'
  · rw [dif_neg hlt]
    have : i = b := by omega
    subst this
    exact ⟨hP, hS⟩

theorem insertionSortM_spec (hswo : SWO lt) (l : List α) (a b : Nat) (hab : a ≤ b)
    (hb : b ≤ l.length) (hinc : KeysInc key l a b) :
    PermIn l (insertionSortM lt l a b) a b ∧
      SortedIn (Tlt lt key) (insertionSortM lt l a b) a b := by
  unfold insertionSortM
  by_cases hab' : a < b
  · exact insOuter_spec hswo l a b hb hinc (a + 1) l (by omega) (by omega)
      (PermIn.refl _ _ _) (sortedIn_nil _ _ _ (Nat.le_refl _))
  · rw [insOuter, dif_neg (by omega)]
    exact ⟨PermIn.refl _ _ _, sortedIn_nil _ _ _ (by omega)⟩

end ins

/-! ### `symMerge` -/

section merge
variable {lt : α → α → Bool} {key : α → Nat}

/-- The keys of `[a, m)` are below those of `[m, b)` (the left run came first). -/
def KeysLR (key : α → Nat) (l : List α) (a m b : Nat) : Prop :=
  ∀ p q x y, a ≤ p → p < m → m ≤ q → q < b → l[p]? = some x → l[q]? = some y → key x < key y

theorem KeysLR.congr {l l' : List α} {a m b : Nat} (h : KeysLR key l a m b)
    (heq : ∀ p, a ≤ p → p < b → l'[p]? = l[p]?) : KeysLR key l' a m b := by
  intro p q x y hp hpm hq hqb hx hy
  rw [heq p hp (by omega)] at hx
  rw [heq q (by omega) hqb] at hy
  exact h p q x y hp hpm hq hqb hx hy

/-- `symMerge`'s first case: `data[a]` inserted into `[m, b)` (`m = a + 1`). -/
theorem symMerge_insLeft (hswo : SWO lt) (l : List α) (a b : Nat) (hab : a + 1 < b)
    (hb : b ≤ l.length) (hR : SortedIn (Tlt lt key) l (a + 1) b)
    (hK : KeysLR key l a (a + 1) b) :
    PermIn l (upM l a (bsearch (fun h => lessL lt l h a) (a + 1) b - 1 - a)) a b ∧
      SortedIn (Tlt lt key) (upM l a (bsearch (fun h => lessL lt l h a) (a + 1) b - 1 - a))
        a b := by
  obtain ⟨k1, k2, k3, k4⟩ := bsearch_spec (fun h => lessL lt l h a) (a + 1) b (by omega)
  generalize bsearch (fun h => lessL lt l h a) (a + 1) b = k at k1 k2 k3 k4
  obtain ⟨hP, hc⟩ := upM_spec l a (k - 1 - a) (by omega)
  refine ⟨hP.mono (Nat.le_refl _) (by omega), ?_⟩
  obtain ⟨x, hx⟩ := getElem?_some_of_lt (show a < l.length by omega)
  intro p q u v hp hpq hq hu hv
  rw [hc] at hu hv
  by_cases hpk : p < k - 1
  · rw [if_pos ⟨hp, by omega⟩] at hu
    by_cases hqk : q < k - 1
    · rw [if_pos ⟨by omega, by omega⟩] at hv
      exact hR (p + 1) (q + 1) u v (by omega) (by omega) (by omega) hu hv
    · by_cases hqk' : q = k - 1
      · rw [if_neg (by omega), if_pos (by omega), hx] at hv
        cases hv
        -- `Less(k-1, a)` was true
        obtain ⟨w, hw⟩ := getElem?_some_of_lt (show k - 1 < l.length by omega)
        have hP1 : lessL lt l (k - 1) a = true := by
          rcases k3 with k3 | k3
          · omega
          · exact k3
        rw [lessL_eq lt l (k - 1) a w x hw hx] at hP1
        exact Tlt_trans_le hswo (hR.le (by omega) (by omega) (by omega) hu hw) (Or.inl hP1)
          (Or.inl rfl)
      · rw [if_neg (by omega), if_neg (by omega)] at hv
        exact hR (p + 1) q u v (by omega) (by omega) hq hu hv
  · by_cases hpk' : p = k - 1
    · rw [if_neg (by omega), if_pos (by omega), hx] at hu
      cases hu
      rw [if_neg (by omega), if_neg (by omega)] at hv
      -- `Less(k, a)` was false
      obtain ⟨w, hw⟩ := getElem?_some_of_lt (show k < l.length by omega)
      have hP0 : lessL lt l k a = false := by
        rcases k4 with k4 | k4
        · omega
        · exact k4
      rw [lessL_eq lt l k a w x hw hx] at hP0
      have hxw : Tlt lt key x w := Or.inr ⟨hP0, hK a k x w (Nat.le_refl _) (by omega) (by omega)
        (by omega) hx hw⟩
      exact Tlt_trans_le hswo (Or.inl rfl) hxw (hR.le (by omega) (by omega) hq hw hv)
    · rw [if_neg (by omega), if_neg (by omega)] at hu hv
      exact hR p q u v (by omega) hpq hq hu hv

/-- `symMerge`'s second case: `data[m]` inserted into `[a, m)` (`b = m + 1`). -/
theorem symMerge_insRight (hswo : SWO lt) (l : List α) (a m : Nat) (ham : a < m)
    (hb : m + 1 ≤ l.length) (hL : SortedIn (Tlt lt key) l a m)
    (hK : KeysLR key l a m (m + 1)) :
    PermIn l (downM l m (m - bsearch (fun h => !lessL lt l m h) a m)) a (m + 1) ∧
      SortedIn (Tlt lt key) (downM l m (m - bsearch (fun h => !lessL lt l m h) a m))
        a (m + 1) := by
  obtain ⟨k1, k2, k3, k4⟩ := bsearch_spec (fun h => !lessL lt l m h) a m (by omega)
  generalize bsearch (fun h => !lessL lt l m h) a m = k at k1 k2 k3 k4
  obtain ⟨hP, hc⟩ := downM_spec l m (m - k) (by omega) (by omega)
  refine ⟨hP.mono (by omega) (Nat.le_refl _), ?_⟩
  obtain ⟨y, hy⟩ := getElem?_some_of_lt (show m < l.length by omega)
  have hmk : m - (m - k) = k := by omega
  rw [hmk] at hc
  intro p q u v hp hpq hq hu hv
  rw [hc] at hu hv
  by_cases hpk : p < k
  · rw [if_neg (by omega), if_neg (by omega)] at hu
    by_cases hqk : q < k
    · rw [if_neg (by omega), if_neg (by omega)] at hv
      exact hL p q u v hp hpq (by omega) hu hv
    · by_cases hqk' : q = k
      · rw [if_neg (by omega), if_pos hqk', hy] at hv
        cases hv
        -- `Less(m, k-1)` was false
        obtain ⟨w, hw⟩ := getElem?_some_of_lt (show k - 1 < l.length by omega)
        have hP1 : lessL lt l m (k - 1) = false := by
          rcases k3 with k3 | k3
          · omega
          · simpa using k3
        rw [lessL_eq lt l m (k - 1) y w hy hw] at hP1
        have hwy : Tlt lt key w y := Or.inr ⟨hP1, hK (k - 1) m w y (by omega) (by omega)
          (Nat.le_refl _) (by omega) hw hy⟩
        exact Tlt_trans_le hswo (hL.le hp (by omega) (by omega) hu hw) hwy (Or.inl rfl)
      · rw [if_pos ⟨by omega, by omega⟩] at hv
        exact hL p (q - 1) u v hp (by omega) (by omega) hu hv
  · by_cases hpk' : p = k
    · rw [if_neg (by omega), if_pos hpk', hy] at hu
      cases hu
      rw [if_pos ⟨by omega, by omega⟩] at hv
      -- `Less(m, k)` was true
      obtain ⟨w, hw⟩ := getElem?_some_of_lt (show k < l.length by omega)
      have hP0 : lessL lt l m k = true := by
        rcases k4 with k4 | k4
        · omega
        · simpa using k4
      rw [lessL_eq lt l m k y w hy hw] at hP0
      exact Tlt_trans_le hswo (Or.inl rfl) (Or.inl hP0)
        (hL.le (by omega) (by omega) (by omega) hw hv)
    · rw [if_pos ⟨by omega, by omega⟩] at hu hv
      exact hL (p - 1) (q - 1) u v (by omega) (by omega) (by omega) hu hv

theorem symMergeM_spec (hswo : SWO lt) :
    ∀ (a m b : Nat) (l : List α), a < m → m < b → b ≤ l.length →
      SortedIn (Tlt lt key) l a m → SortedIn (Tlt lt key) l m b → KeysLR key l a m b →
      PermIn l (symMergeM lt l a m b) a b ∧ SortedIn (Tlt lt key) (symMergeM lt l a m b) a b := by
  intro a m b
  induction h : b - a using Nat.strongRecOn generalizing a m b with
  | _ nn ih =>
  intro l ham hmb hb hSL hSR hK
  rw [symMergeM, dif_pos ⟨ham, hmb⟩]
  by_cases h1 : m - a = 1
  · rw [if_pos h1]
    have : m = a + 1 := by omega
    subst this
    exact symMerge_insLeft hswo l a b (by omega) hb hSR hK
  rw [if_neg h1]
  by_cases h2 : b - m = 1
  · rw [if_pos h2]
    have : b = m + 1 := by omega
    subst this
    exact symMerge_insRight hswo l a m ham hb hSL hK
  rw [if_neg h2]
  simp only []
  generalize hmid : (a + b) / 2 = mid
  have hmid1 : a < mid := by omega
  have hmid2 : mid < b := by omega
  have hmid3 : mid - a ≤ b - mid := by omega
  -- the binary search's range
  have hF : a ≤ (if mid < m then mid + m - b else a) ∧
      (if mid < m then mid + m - b else a) ≤ (if mid < m then mid else m) ∧
      (if mid < m then mid else m) ≤ m ∧ (if mid < m then mid else m) ≤ mid ∧
      mid + m - (if mid < m then mid + m - b else a) ≤ b ∧
      ((if mid < m then mid + m - b else a) = a ∨
        mid + m - (if mid < m then mid + m - b else a) = b) ∧
      ((if mid < m then mid else m) = m ∨ (if mid < m then mid else m) = mid) := by
    split <;> omega
  generalize (if mid < m then mid + m - b else a) = s0 at hF ⊢
  generalize (if mid < m then mid else m) = r0 at hF ⊢
  obtain ⟨F1, F2, F3, F4, F5, F6, F7⟩ := hF
  obtain ⟨k1, k2, k3, k4⟩ := bsearch_spec (fun c => !lessL lt l (mid + m - 1 - c) c) s0 r0 F2
  generalize bsearch (fun c => !lessL lt l (mid + m - 1 - c) c) s0 r0 = start at k1 k2 k3 k4 ⊢
  -- `end` is `mid + m - start`: `[start, mid)` gets `[m, end)`, `[mid, end)` gets `[start, m)`
  generalize he : mid + m - start = e
  have he1 : m ≤ e := by omega
  have he2 : e ≤ b := by omega
  have he3 : e - mid = m - start := by omega
  -- the rotation
  have hrot : PermIn l (if start < m ∧ m < e then rotateM l start m e else l) a b ∧
      ∀ q, (if start < m ∧ m < e then rotateM l start m e else l)[q]? =
        if start ≤ q ∧ q < mid then l[q + (m - start)]?
        else if mid ≤ q ∧ q < e then l[q - (mid - start)]? else l[q]? := by
    split
    · obtain ⟨hp, hc⟩ := rotLoop_spec l m (m - start) (e - m) (by omega) (by omega)
      refine ⟨hp.mono (by omega) (by omega), fun q => ?_⟩
      unfold rotateM
      rw [hc]
      ifs_close
    · refine ⟨PermIn.refl _ _ _, fun q => ?_⟩
      ifs_close
  generalize (if start < m ∧ m < e then rotateM l start m e else l) = l1 at hrot ⊢
  obtain ⟨hP1, hc1⟩ := hrot
  have hl1len := hP1.length
  have c1 : ∀ q, a ≤ q → q < start → l1[q]? = l[q]? := by
    intro q h1 h2; rw [hc1]; ifs_close
  have c2 : ∀ q, start ≤ q → q < mid → l1[q]? = l[q + (m - start)]? := by
    intro q h1 h2; rw [hc1]; ifs_close
  have c3 : ∀ q, mid ≤ q → q < e → l1[q]? = l[q - (mid - start)]? := by
    intro q h1 h2; rw [hc1]; ifs_close
  have c4 : ∀ q, e ≤ q → q < b → l1[q]? = l[q]? := by
    intro q h1 h2; rw [hc1]; ifs_close
  -- the runs of `l1`
  have SL1 : SortedIn (Tlt lt key) l1 a start := by
    intro p q x y hp hpq hq hx hy
    rw [c1 p hp (by omega)] at hx; rw [c1 q (by omega) hq] at hy
    exact hSL p q x y hp hpq (by omega) hx hy
  have SR1 : SortedIn (Tlt lt key) l1 start mid := by
    intro p q x y hp hpq hq hx hy
    rw [c2 p hp (by omega)] at hx; rw [c2 q (by omega) hq] at hy
    exact hSR _ _ x y (by omega) (by omega) (by omega) hx hy
  have K1 : KeysLR key l1 a start mid := by
    intro p q x y hp hpm hq hqb hx hy
    rw [c1 p hp hpm] at hx; rw [c2 q hq hqb] at hy
    exact hK _ _ x y hp (by omega) (by omega) (by omega) hx hy
  have SL2 : SortedIn (Tlt lt key) l1 mid e := by
    intro p q x y hp hpq hq hx hy
    rw [c3 p hp (by omega)] at hx; rw [c3 q (by omega) hq] at hy
    exact hSL _ _ x y (by omega) (by omega) (by omega) hx hy
  have SR2 : SortedIn (Tlt lt key) l1 e b := by
    intro p q x y hp hpq hq hx hy
    rw [c4 p hp (by omega)] at hx; rw [c4 q (by omega) hq] at hy
    exact hSR _ _ x y (by omega) hpq hq hx hy
  have K2 : KeysLR key l1 mid e b := by
    intro p q x y hp hpm hq hqb hx hy
    rw [c3 p hp hpm] at hx; rw [c4 q hq hqb] at hy
    exact hK _ _ x y (by omega) (by omega) (by omega) hqb hx hy
  -- every element of `l1[a, mid)` is below every element of `l1[mid, b)`
  have cross : ∀ p q x y, a ≤ p → p < mid → mid ≤ q → q < b → l1[p]? = some x →
      l1[q]? = some y → Tlt lt key x y := by
    intro p q x y hp hpm hq hqb hx hy
    by_cases hps : p < start
    · rw [c1 p hp hps] at hx
      by_cases hqe : q < e
      · -- left run with left run
        rw [c3 q hq hqe] at hy
        exact hSL _ _ x y hp (by omega) (by omega) hx hy
      · -- left with right: `Less(end, start-1)` was false
        rw [c4 q (by omega) hqb] at hy
        have hns : start ≠ s0 := by omega
        have hP := k3.resolve_left hns
        rw [show mid + m - 1 - (start - 1) = e by omega] at hP
        obtain ⟨w1, hw1⟩ := getElem?_some_of_lt (show start - 1 < l.length by omega)
        obtain ⟨w2, hw2⟩ := getElem?_some_of_lt (show e < l.length by omega)
        have hP' : lessL lt l e (start - 1) = false := by simpa using hP
        rw [lessL_eq lt l e (start - 1) w2 w1 hw2 hw1] at hP'
        have hT : Tlt lt key w1 w2 := Or.inr ⟨hP', hK _ _ w1 w2 (by omega) (by omega) (by omega)
          (by omega) hw1 hw2⟩
        exact Tlt_trans_le hswo (hSL.le hp (by omega) (by omega) hx hw1) hT
          (hSR.le (by omega) (by omega) hqb hw2 hy)
    · rw [c2 p (by omega) hpm] at hx
      by_cases hqe : q < e
      · -- right with left: `Less(end-1, start)` was true
        rw [c3 q hq hqe] at hy
        have hns : start ≠ r0 := by omega
        have hP := k4.resolve_left hns
        rw [show mid + m - 1 - start = e - 1 by omega] at hP
        obtain ⟨w1, hw1⟩ := getElem?_some_of_lt (show e - 1 < l.length by omega)
        obtain ⟨w2, hw2⟩ := getElem?_some_of_lt (show start < l.length by omega)
        have hP' : lessL lt l (e - 1) start = true := by simpa using hP
        rw [lessL_eq lt l (e - 1) start w1 w2 hw1 hw2] at hP'
        exact Tlt_trans_le hswo (hSR.le (by omega) (by omega) (by omega) hx hw1) (Or.inl hP')
          (hSL.le (Nat.le_trans F1 k1) (by omega) (by omega) hw2 hy)
      · -- right run with right run
        rw [c4 q (by omega) hqb] at hy
        exact hSR _ _ x y (by omega) (by omega) hqb hx hy
  -- the first recursive call, on `[a, mid)`
  have hrec1 : PermIn l1 (if a < start ∧ start < mid then symMergeM lt l1 a start mid else l1)
      a mid ∧ SortedIn (Tlt lt key)
        (if a < start ∧ start < mid then symMergeM lt l1 a start mid else l1) a mid := by
    split
    · rename_i hc
      exact ih (mid - a) (by omega) a start mid rfl l1 hc.1 hc.2 (by omega) SL1 SR1 K1
    · refine ⟨PermIn.refl _ _ _, ?_⟩
      by_cases hsa : start = a
      · subst hsa; exact SR1
      · have : start = mid := by omega
        subst this; exact SL1
  generalize (if a < start ∧ start < mid then symMergeM lt l1 a start mid else l1) = l2
    at hrec1 ⊢
  obtain ⟨hP2, hS2⟩ := hrec1
  have hl2len := hP2.length
  have c5 : ∀ q, mid ≤ q → l2[q]? = l1[q]? := fun q hq => hP2.2 q (Or.inr hq)
  -- the second, on `[mid, b)`
  have hrec2 : PermIn l2 (if mid < e ∧ e < b then symMergeM lt l2 mid e b else l2) mid b ∧
      SortedIn (Tlt lt key) (if mid < e ∧ e < b then symMergeM lt l2 mid e b else l2) mid b := by
    have SL2' := SL2.congr (fun q hq _ => c5 q hq)
    have SR2' := SR2.congr (fun q hq _ => c5 q (by omega))
    split
    · rename_i hc
      exact ih (b - mid) (by omega) mid e b rfl l2 hc.1 hc.2 (by omega) SL2' SR2'
        (K2.congr (fun q hq _ => c5 q hq))
    · refine ⟨PermIn.refl _ _ _, ?_⟩
      by_cases hem : e = mid
      · subst hem; exact SR2'
      · have : e = b := by omega
        subst this; exact SL2'
  generalize (if mid < e ∧ e < b then symMergeM lt l2 mid e b else l2) = l3 at hrec2 ⊢
  obtain ⟨hP3, hS3⟩ := hrec2
  refine ⟨hP1.trans ((hP2.mono (Nat.le_refl _) (by omega)).trans
    (hP3.mono (by omega) (Nat.le_refl _))), ?_⟩
  apply sortedIn_join (m := mid) _ hS3
  · intro p q x y hp hpm hq hqb hx hy
    rw [hP3.2 p (Or.inl hpm)] at hx
    obtain ⟨p', hp1, hp2, hp'⟩ := hP2.segFrom (by omega) (by omega) ⟨hp, hpm⟩ hx
    obtain ⟨q', hq1, hq2, hq'⟩ := hP3.segFrom (by omega) (by omega) ⟨hq, hqb⟩ hy
    rw [c5 q' hq1] at hq'
    exact cross p' q' x y hp1 hp2 hq1 hq2 hp' hq'
  · exact hS2.congr (fun q _ hq => hP3.2 q (Or.inl hq))

end merge

/-! ### `stable` -/

section stable
variable {lt : α → α → Bool} {key : α → Nat}

/-- The element at `p ∈ [s, e)` has a key in `p`'s block of size `bs`. -/
def KeyBlockIn (key : α → Nat) (bs : Nat) (l : List α) (s e : Nat) : Prop :=
  ∀ p x, s ≤ p → p < e → l[p]? = some x → key x / bs = p / bs

/-- Every block of size `bs` below `u` is sorted. -/
def BlockSorted (R : α → α → Prop) (bs : Nat) (l : List α) (u : Nat) : Prop :=
  ∀ p q x y, p < q → q < u → p / bs = q / bs → l[p]? = some x → l[q]? = some y → R x y

theorem div_eq_blk {bs k p : Nat} (h1 : k * bs ≤ p) (h2 : p < k * bs + bs) : p / bs = k :=
  Nat.div_eq_of_lt_le h1 (by rw [Nat.succ_mul]; exact h2)

theorem div2_eq {bs x y : Nat} (h : x / bs = y / bs) : x / (bs * 2) = y / (bs * 2) := by
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

/-- The insertion sorts of `stable`'s first loop, from `a = 20 c`. -/
theorem insPhase_spec (hswo : SWO lt) (l0 : List α) (n : Nat) (hn : l0.length = n)
    (hpos : ∀ p x, l0[p]? = some x → key x = p) :
    ∀ c (L : List α), c * 20 ≤ n → PermIn l0 L 0 (c * 20) → KeyBlockIn key 20 L 0 n →
      BlockSorted (Tlt lt key) 20 L (c * 20) →
      (insPhase lt n (c * 20) L).Perm l0 ∧ KeyBlockIn key 20 (insPhase lt n (c * 20) L) 0 n ∧
        BlockSorted (Tlt lt key) 20 (insPhase lt n (c * 20) L) n := by
  intro c
  induction h : n - c * 20 using Nat.strongRecOn generalizing c with
  | _ nn ih =>
  intro L hc hP hKB hBS
  have hLlen := hP.length
  -- one block, `[a, b')`
  have step : ∀ b', c * 20 ≤ b' → b' ≤ n → b' ≤ c * 20 + 20 →
      PermIn l0 (insertionSortM lt L (c * 20) b') 0 b' ∧
      KeyBlockIn key 20 (insertionSortM lt L (c * 20) b') 0 n ∧
      BlockSorted (Tlt lt key) 20 (insertionSortM lt L (c * 20) b') b' := by
    intro b' hb1 hb2 hb3
    have hinc : KeysInc key L (c * 20) b' := by
      intro p q x y hp hpq hq hx hy
      rw [hP.2 p (Or.inr hp)] at hx; rw [hP.2 q (Or.inr (by omega))] at hy
      rw [hpos p x hx, hpos q y hy]; exact hpq
    obtain ⟨hP', hS'⟩ := insertionSortM_spec hswo L (c * 20) b' hb1 (by omega) hinc
    refine ⟨(hP.mono (Nat.le_refl _) hb1).trans (hP'.mono (Nat.zero_le _) (Nat.le_refl _)),
      ?_, ?_⟩
    · intro p x hp hpn hx
      by_cases hin : c * 20 ≤ p ∧ p < b'
      · obtain ⟨q, hq1, hq2, hq⟩ := hP'.segFrom hb1 (by omega) hin hx
        rw [hP.2 q (Or.inr hq1)] at hq
        rw [hpos q x hq, div_eq_blk (k := c) hq1 (by omega), div_eq_blk (k := c) hin.1 (by omega)]
      · rw [hP'.2 p (by omega)] at hx
        exact hKB p x hp hpn hx
    · intro p q x y hpq hq hblk hx hy
      by_cases hpa : c * 20 ≤ p
      · exact hS' p q x y hpa hpq hq hx hy
      · by_cases hqa : q < c * 20
        · rw [hP'.2 p (Or.inl (by omega))] at hx; rw [hP'.2 q (Or.inl hqa)] at hy
          exact hBS p q x y hpq hqa hblk hx hy
        · exfalso
          have h1 : p / 20 < c := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
          have h2 : c ≤ q / 20 := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
          omega
  rw [insPhase]
  by_cases hlt : c * 20 + 20 ≤ n
  · rw [dif_pos hlt]
    obtain ⟨hP', hKB', hBS'⟩ := step (c * 20 + 20) (by omega) hlt (Nat.le_refl _)
    have := ih (n - (c + 1) * 20) (by rw [Nat.succ_mul]; omega) (c + 1) rfl
      (insertionSortM lt L (c * 20) (c * 20 + 20)) (by rw [Nat.succ_mul]; omega)
      (by rw [Nat.succ_mul]; exact hP') hKB' (by rw [Nat.succ_mul]; exact hBS')
    rw [Nat.succ_mul] at this
    exact this
  · rw [dif_neg hlt]
    obtain ⟨hP', hKB', hBS'⟩ := step n hc (Nat.le_refl _) (by omega)
    exact ⟨hP'.1, hKB', hBS'⟩

/-- The merges of one iteration of `stable`'s second loop, from `a = 2 bs c`. -/
theorem mergeLevel_spec (hswo : SWO lt) (L0 : List α) (n bs : Nat) (hbs : 0 < bs)
    (hn : L0.length = n) (hKB0 : KeyBlockIn key bs L0 0 n) (hBS0 : BlockSorted (Tlt lt key) bs L0 n) :
    ∀ c (L : List α), c * (bs * 2) ≤ n → PermIn L0 L 0 (c * (bs * 2)) →
      KeyBlockIn key (bs * 2) L 0 (c * (bs * 2)) →
      BlockSorted (Tlt lt key) (bs * 2) L (c * (bs * 2)) →
      (mergeLevel lt n bs (c * (bs * 2)) L).Perm L0 ∧
        KeyBlockIn key (bs * 2) (mergeLevel lt n bs (c * (bs * 2)) L) 0 n ∧
        BlockSorted (Tlt lt key) (bs * 2) (mergeLevel lt n bs (c * (bs * 2)) L) n := by
  intro c
  induction h : n - c * (bs * 2) using Nat.strongRecOn generalizing c with
  | _ nn ih =>
  intro L hc hP hKB hBS
  have hLlen := hP.length
  have hL0 : ∀ p, c * (bs * 2) ≤ p → L[p]? = L0[p]? := fun p hp => hP.2 p (Or.inr hp)
  generalize hA : c * bs = A at *
  have hA2 : c * (bs * 2) = 2 * A := by rw [← hA, ← Nat.mul_assoc, Nat.mul_comm c bs,
    Nat.mul_comm, ← Nat.mul_assoc, Nat.mul_comm 2 bs]
  rw [hA2] at hc hP hKB hBS hL0 ⊢
  have blkL : ∀ p, 2 * A ≤ p → p < 2 * A + bs → p / bs = 2 * c := by
    intro p h1 h2; apply div_eq_blk <;> rw [Nat.mul_comm 2 c, Nat.mul_assoc, Nat.mul_comm 2 bs,
      ← Nat.mul_assoc, hA] <;> omega
  have blkR : ∀ p, 2 * A + bs ≤ p → p < 2 * A + 2 * bs → p / bs = 2 * c + 1 := by
    intro p h1 h2; apply div_eq_blk <;> rw [Nat.succ_mul, Nat.mul_comm 2 c, Nat.mul_assoc,
      Nat.mul_comm 2 bs, ← Nat.mul_assoc, hA] <;> omega
  have blk2 : ∀ p, 2 * A ≤ p → p < 2 * A + 2 * bs → p / (bs * 2) = c := by
    intro p h1 h2; apply div_eq_blk <;> rw [← Nat.mul_assoc, hA] <;> omega
  -- `[a, e')` merged (or left as it is, when it is one block of `bs`)
  have step : ∀ e', 2 * A + bs < e' → e' ≤ n → e' ≤ 2 * A + 2 * bs →
      PermIn L0 (symMergeM lt L (2 * A) (2 * A + bs) e') 0 e' ∧
      KeyBlockIn key (bs * 2) (symMergeM lt L (2 * A) (2 * A + bs) e') 0 e' ∧
      BlockSorted (Tlt lt key) (bs * 2) (symMergeM lt L (2 * A) (2 * A + bs) e') e' := by
    intro e' he1 he2 he3
    have hSL : SortedIn (Tlt lt key) L (2 * A) (2 * A + bs) := by
      intro p q x y hp hpq hq hx hy
      rw [hL0 p hp] at hx; rw [hL0 q (by omega)] at hy
      exact hBS0 p q x y hpq (by omega) (by rw [blkL p hp (by omega), blkL q (by omega) hq])
        hx hy
    have hSR : SortedIn (Tlt lt key) L (2 * A + bs) e' := by
      intro p q x y hp hpq hq hx hy
      rw [hL0 p (by omega)] at hx; rw [hL0 q (by omega)] at hy
      exact hBS0 p q x y hpq (by omega)
        (by rw [blkR p hp (by omega), blkR q (by omega) (by omega)]) hx hy
    have hK : KeysLR key L (2 * A) (2 * A + bs) e' := by
      intro p q x y hp hpm hq hqb hx hy
      rw [hL0 p hp] at hx; rw [hL0 q (by omega)] at hy
      have k1 := hKB0 p x (Nat.zero_le _) (by omega) hx
      have k2 := hKB0 q y (Nat.zero_le _) (by omega) hy
      rw [blkL p hp hpm] at k1; rw [blkR q hq (by omega)] at k2
      exact Nat.lt_of_div_lt_div (c := bs) (by omega)
    obtain ⟨hP', hS'⟩ := symMergeM_spec hswo (2 * A) (2 * A + bs) e' L (by omega) he1
      (by omega) hSL hSR hK
    refine ⟨(hP.mono (Nat.le_refl _) (by omega)).trans (hP'.mono (Nat.zero_le _) (by omega)),
      ?_, ?_⟩
    · intro p x hp hpn hx
      by_cases hin : 2 * A ≤ p
      · obtain ⟨q, hq1, hq2, hq⟩ := hP'.segFrom (by omega) (by omega) ⟨hin, hpn⟩ hx
        rw [hL0 q hq1] at hq
        rw [div2_eq (hKB0 q x (Nat.zero_le _) (by omega) hq), blk2 q hq1 (by omega),
          blk2 p hin (by omega)]
      · rw [hP'.2 p (Or.inl (by omega))] at hx
        exact hKB p x hp (by omega) hx
    · intro p q x y hpq hq hblk hx hy
      by_cases hpa : 2 * A ≤ p
      · exact hS' p q x y hpa hpq hq hx hy
      · by_cases hqa : q < 2 * A
        · rw [hP'.2 p (Or.inl (by omega))] at hx; rw [hP'.2 q (Or.inl hqa)] at hy
          exact hBS p q x y hpq hqa hblk hx hy
        · exfalso
          have h1 : p / (bs * 2) < c := (Nat.div_lt_iff_lt_mul (by omega)).2
            (by rw [hA2]; omega)
          rw [blk2 q (by omega) (by omega)] at hblk
          omega
  rw [mergeLevel]
  by_cases hlt : 0 < bs ∧ 2 * A + 2 * bs ≤ n
  · rw [dif_pos hlt]
    obtain ⟨hP', hKB', hBS'⟩ := step (2 * A + 2 * bs) (by omega) hlt.2 (Nat.le_refl _)
    have e1 : (c + 1) * (bs * 2) = 2 * A + 2 * bs := by
      rw [Nat.succ_mul, ← hA2]; omega
    have := ih (n - (c + 1) * (bs * 2)) (by omega) (c + 1) rfl
      (symMergeM lt L (2 * A) (2 * A + bs) (2 * A + 2 * bs)) (by omega)
      (by rw [e1]; exact hP') (by rw [e1]; exact hKB') (by rw [e1]; exact hBS')
    rw [e1] at this
    exact this
  · rw [dif_neg hlt]
    by_cases hm : 2 * A + bs < n
    · rw [if_pos hm]
      obtain ⟨hP', hKB', hBS'⟩ := step n hm (Nat.le_refl _) (by omega)
      exact ⟨hP'.1, hKB', hBS'⟩
    · rw [if_neg hm]
      refine ⟨hP.1, ?_, ?_⟩
      · intro p x hp hpn hx
        by_cases hin : 2 * A ≤ p
        · rw [hL0 p hin] at hx
          rw [div2_eq (hKB0 p x hp hpn hx)]
        · exact hKB p x hp (by omega) hx
      · intro p q x y hpq hq hblk hx hy
        by_cases hpa : 2 * A ≤ p
        · rw [hL0 p hpa] at hx; rw [hL0 q (by omega)] at hy
          exact hBS0 p q x y hpq hq (by rw [blkL p hpa (by omega), blkL q (by omega) (by omega)])
            hx hy
        · by_cases hqa : q < 2 * A
          · exact hBS p q x y hpq hqa hblk hx hy
          · exfalso
            have h1 : p / (bs * 2) < c := (Nat.div_lt_iff_lt_mul (by omega)).2
              (by rw [hA2]; omega)
            rw [blk2 q (by omega) (by omega)] at hblk
            omega

/-- `stable`'s second loop, from `blockSize = bs`. -/
theorem mergePhase_spec (hswo : SWO lt) (l0 : List α) (n : Nat) (hn : l0.length = n) :
    ∀ bs (L : List α), 0 < bs → L.Perm l0 → KeyBlockIn key bs L 0 n →
      BlockSorted (Tlt lt key) bs L n →
      (mergePhase lt n bs L).Perm l0 ∧ SortedIn (Tlt lt key) (mergePhase lt n bs L) 0 n := by
  intro bs
  induction h : n - bs using Nat.strongRecOn generalizing bs with
  | _ nn ih =>
  intro L hbs hP hKB hBS
  have hLlen := hP.length_eq
  rw [mergePhase]
  by_cases hlt : 0 < bs ∧ bs < n
  · rw [dif_pos hlt]
    obtain ⟨hP', hKB', hBS'⟩ := mergeLevel_spec hswo L n bs hbs (by omega) hKB hBS 0 L
      (by omega) (PermIn.refl _ _ _) (fun _ _ _ _ _ => by omega) (fun _ _ _ _ _ _ => by omega)
    rw [Nat.zero_mul] at hP' hKB' hBS'
    rw [show 2 * bs = bs * 2 from Nat.mul_comm 2 bs]
    exact ih (n - bs * 2) (by omega) (bs * 2) rfl _ (by omega) (hP'.trans hP) hKB' hBS'
  · rw [dif_neg hlt]
    refine ⟨hP, fun p q x y _ hpq hq hx hy => hBS p q x y hpq hq ?_ hx hy⟩
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

/-- **`stable` sorts by `Tlt`** a list whose keys are the positions. -/
theorem stableM_spec (hswo : SWO lt) (l0 : List α)
    (hpos : ∀ p x, l0[p]? = some x → key x = p) :
    (stableM lt l0 l0.length).Perm l0 ∧
      SortedIn (Tlt lt key) (stableM lt l0 l0.length) 0 l0.length := by
  unfold stableM
  obtain ⟨hP, hKB, hBS⟩ := insPhase_spec (key := key) hswo l0 l0.length rfl hpos 0 l0
    (by omega) (PermIn.refl _ _ _)
    (fun p x _ _ hx => by rw [hpos p x hx]) (fun _ _ _ _ _ _ _ => by omega)
  rw [Nat.zero_mul] at hP hKB hBS
  exact mergePhase_spec hswo l0 l0.length rfl 20 _ (by omega) hP hKB hBS

end stable

/-! ### The stable sort -/

/-- **The model of `stable`, run on `l` tagged with its positions and compared by `lt` on the
elements, is `List.mergeSort`'s stable sort** by "`a` may stay before `b` unless `b < a`". -/
theorem stableM_eq_mergeSort {E : Type} (lt : E → E → Bool) (hswo : SWO lt) (l : List E) :
    (stableM (fun x y : E × Nat => lt x.1 y.1) l.zipIdx l.length).map Prod.fst =
      l.mergeSort (fun a b => !lt b a) := by
  have hswo' : SWO (fun x y : E × Nat => lt x.1 y.1) :=
    ⟨fun x => hswo.irrefl x.1, fun x y z => hswo.trans x.1 y.1 z.1,
      fun x y z => hswo.ntrans x.1 y.1 z.1⟩
  have hpos : ∀ p (x : E × Nat), l.zipIdx[p]? = some x → x.2 = p := by
    intro p x hx
    rw [List.getElem?_zipIdx] at hx
    cases h : l[p]? with
    | none => rw [h] at hx; cases hx
    | some y => rw [h] at hx; cases hx; simp
  have hlen : l.zipIdx.length = l.length := List.length_zipIdx
  obtain ⟨hP, hS⟩ := stableM_spec (key := Prod.snd) hswo' l.zipIdx hpos
  rw [hlen] at hP hS
  generalize stableM (fun x y : E × Nat => lt x.1 y.1) l.zipIdx l.length = R at hP hS
  have hRlen : R.length = l.length := by rw [hP.length_eq, hlen]
  let le : E → E → Bool := fun a b => !lt b a
  have hpw : R.Pairwise (fun a b => List.zipIdxLE le a b = true) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hT := hS i j R[i] R[j] (Nat.zero_le _) hij (by omega) (by simp) (by simp)
    unfold Tlt at hT
    simp only [List.zipIdxLE, le]
    rcases hT with hT | ⟨hT1, hT2⟩
    · simp only at hT
      simp [hswo.asymm hT, hT]
    · simp only at hT1
      by_cases h : lt R[i].1 R[j].1 = true <;> simp [hT1, h]
      omega
  have hms := List.pairwise_mergeSort (le := List.zipIdxLE le)
    (List.zipIdxLE_trans (fun a b c h1 h2 => by
      simp only [le, Bool.not_eq_eq_eq_not, Bool.not_true] at h1 h2 ⊢
      exact hswo.ntrans c b a h2 h1))
    (List.zipIdxLE_total (fun a b => by
      simp only [le]
      cases h : lt b a
      · simp
      · simp [hswo.asymm h]))
    l.zipIdx
  have heq : R = l.zipIdx.mergeSort (List.zipIdxLE le) := by
    apply List.Perm.eq_of_pairwise _ hpw hms (hP.trans (List.mergeSort_perm _ _).symm)
    intro x y hx hy hxy hyx
    have hx' : x ∈ l.zipIdx := hP.subset hx
    have hy' : y ∈ l.zipIdx := List.mem_mergeSort.1 hy
    have hk : x.2 = y.2 := by
      simp only [List.zipIdxLE, le] at hxy hyx
      by_cases h1 : lt x.1 y.1 = true <;> by_cases h2 : lt y.1 x.1 = true <;>
        simp [h1, h2] at hxy hyx
      omega
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hy'
    have h1 := hpos i x hi
    have h2 := hpos j y hj
    have : i = j := by omega
    subst this
    rw [hi] at hj; cases hj; rfl
  rw [heq]
  exact List.mergeSort_zipIdx

end stableModel
end EtcdGrove
end Perennial
