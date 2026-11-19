/-
**`value.Compare`'s order** (structured-merge-diff v7.0.0): the fuel lemma of `UVal.compareF`
(any fuel above `size a + size b` gives `UVal.compare a b`), the list and map cases as
lexicographic comparisons (`listCmp`), and the order laws of `UVal.compare` (`compare_eq_zero`,
`compare_antisymm`, `compare_trans`), which hold on all values (the laws' canonicity premises
are not needed). Prove phase (2026-11-19).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

namespace ValueCompare

open ValuePure

/-! ## Lexicographic comparison -/

/-- The lexicographic comparison of two lists by `f`. -/
def listCmp {α : Type} (f : α → α → Int) : List α → List α → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys => if f x y = 0 then listCmp f xs ys else f x y

/-- Map entries: by key (`gsCompare`), then by value (`f`). -/
def pairCmp (f : UVal → UVal → Int) (p q : GoString × UVal) : Int :=
  if gsCompare p.1 q.1 = 0 then f p.2 q.2 else gsCompare p.1 q.1

theorem listCmp_congr {α : Type} (f g : α → α → Int) : ∀ (xs ys : List α),
    (∀ x ∈ xs, ∀ y ∈ ys, f x y = g x y) → listCmp f xs ys = listCmp g xs ys
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | x :: xs, y :: ys, h => by
      simp only [listCmp]
      rw [h x (by simp) y (by simp),
        listCmp_congr f g xs ys (fun a ha b hb => h a (by simp [ha]) b (by simp [hb]))]

/-! ## Unfolding `compareF` -/

/-- The list case's fold step. -/
def listStep (f : UVal → UVal → Int) : Int → UVal × UVal → Int :=
  fun c (a, b) => if c != 0 then c else f a b

/-- The map case's fold step. -/
def mapStep (L1 L2 : Nat) (f : UVal → UVal → Int) :
    (Int × Nat × Bool) → (GoString × Option UVal × Option UVal) → (Int × Nat × Bool) :=
  fun (c, i, stop) (_, l, r) =>
    if stop then (c, i, stop) else
    let c :=
      if i == L1 then -1
      else if i == L2 then 1
      else match l, r with
        | none, _ => 1
        | _, none => -1
        | some l, some r => f l r
    (c, i + 1, c != 0)

theorem compareF_list_raw (n : Nat) (xs ys : List UVal) :
    UVal.compareF (n + 1) (.list xs) (.list ys) =
      (let r := (xs.zip ys).foldl (listStep (UVal.compareF n)) 0
       if r != 0 then r else if xs.length < ys.length then -1
       else if ys.length < xs.length then 1 else 0) := by
  rfl

theorem compareF_map_raw (n : Nat) (xs ys : List (GoString × UVal)) :
    UVal.compareF (n + 1) (.map xs) (.map ys) =
      (if xs.length == 0 && ys.length == 0 then 0 else
       ((zipLexical (xs.length + ys.length + 1) xs ys).foldl
         (mapStep xs.length ys.length (UVal.compareF n)) (0, 0, false)).1) := by
  rfl


theorem listStep_stop (f : UVal → UVal → Int) : ∀ (z : List (UVal × UVal)) (c : Int), c ≠ 0 →
    z.foldl (listStep f) c = c
  | [], _, _ => rfl
  | p :: z, c, h => by
      simp only [List.foldl_cons]
      have : listStep f c p = c := by simp [listStep, h]
      rw [this, listStep_stop f z c h]

theorem listFold_eq (f : UVal → UVal → Int) : ∀ (xs ys : List UVal),
    (let r := (xs.zip ys).foldl (listStep f) 0
     if r != 0 then r else if xs.length < ys.length then -1
     else if ys.length < xs.length then 1 else 0) = listCmp f xs ys
  | [], [] => rfl
  | [], _ :: _ => by simp [listCmp]
  | _ :: _, [] => by simp [listCmp]
  | x :: xs, y :: ys => by
      have ih := listFold_eq f xs ys
      simp only [List.zip_cons_cons, List.foldl_cons, List.length_cons] at ih ⊢
      have h0 : listStep f 0 (x, y) = f x y := by simp [listStep]
      rw [h0]
      by_cases hc : f x y = 0
      · rw [hc]; simp only [listCmp, hc, ite_true]; rw [← ih]
        simp only [Nat.add_lt_add_iff_right]
      · rw [listStep_stop f _ _ hc]; simp [listCmp, hc]

theorem compareF_list (n : Nat) (xs ys : List UVal) :
    UVal.compareF (n + 1) (.list xs) (.list ys) = listCmp (UVal.compareF n) xs ys := by
  rw [compareF_list_raw, listFold_eq]

theorem mapStep_stop (L1 L2 : Nat) (f : UVal → UVal → Int) :
    ∀ (z : List (GoString × Option UVal × Option UVal)) (c : Int) (i : Nat),
    z.foldl (mapStep L1 L2 f) (c, i, true) = (c, i, true)
  | [], _, _ => rfl
  | p :: z, c, i => by
      simp only [List.foldl_cons]
      have : mapStep L1 L2 f (c, i, true) p = (c, i, true) := by simp [mapStep]
      rw [this, mapStep_stop L1 L2 f z c i]

theorem gsCompare_eq_zero_iff (a b : GoString) : gsCompare a b = 0 ↔ a = b :=
  ⟨gsCompare_eq_zero a b, fun h => h ▸ gsCompare_self a⟩

theorem mapFold_eq (L1 L2 : Nat) (f : UVal → UVal → Int) : ∀ (n : Nat) (xs ys : List (GoString × UVal))
    (i : Nat), L1 = i + xs.length → L2 = i + ys.length → xs.length + ys.length + 1 ≤ n →
    ((zipLexical n xs ys).foldl (mapStep L1 L2 f) (0, i, false)).1 = listCmp (pairCmp f) xs ys
  | 0, _, _, _, _, _, h => by omega
  | n + 1, [], [], i, _, _, _ => by simp [zipLexical, listCmp]
  | n + 1, (k, a) :: xs, [], i, h1, h2, _ => by
      simp only [zipLexical, List.foldl_cons, listCmp]
      have : mapStep L1 L2 f (0, i, false) (k, some a, none) = (1, i + 1, true) := by
        simp only [List.length_cons] at h1
        simp [mapStep, h2]; omega
      rw [this, mapStep_stop]
  | n + 1, [], (k, b) :: ys, i, h1, h2, _ => by
      simp only [zipLexical, List.foldl_cons, listCmp]
      have : mapStep L1 L2 f (0, i, false) (k, none, some b) = (-1, i + 1, true) := by
        simp [mapStep, h1]
      rw [this, mapStep_stop]
  | n + 1, (k, a) :: xs, (k', b) :: ys, i, h1, h2, hn => by
      simp only [List.length_cons] at h1 h2 hn
      have hi1 : (i == L1) = false := by simp; omega
      have hi2 : (i == L2) = false := by simp; omega
      simp only [zipLexical, listCmp, pairCmp]
      by_cases hk : k = k'
      · subst hk
        simp only [ite_true, gsCompare_self, List.foldl_cons]
        have : mapStep L1 L2 f (0, i, false) (k, some a, some b) = (f a b, i + 1, f a b != 0) := by
          simp [mapStep, hi1, hi2]
        rw [this]
        by_cases hc : f a b = 0
        · rw [hc]; simp only [ite_true, bne_self_eq_false]
          exact mapFold_eq L1 L2 f n xs ys (i + 1) (by omega) (by omega) (by omega)
        · have : (f a b != 0) = true := by simp [hc]
          rw [this, mapStep_stop]; simp [hc]
      · have hne : ¬ gsCompare k k' = 0 := by rw [gsCompare_eq_zero_iff]; exact hk
        simp only [hk, ite_false, hne]
        by_cases hlt : gsLt k k' = true
        · simp only [hlt, ite_true, List.foldl_cons]
          have : mapStep L1 L2 f (0, i, false) (k, some a, none) = (-1, i + 1, true) := by
            simp [mapStep, hi1, hi2]
          rw [this, mapStep_stop]
          exact ((gsLt_iff k k').1 hlt).symm
        · simp only [hlt, ite_false, Bool.false_eq_true, List.foldl_cons]
          have : mapStep L1 L2 f (0, i, false) (k', none, some b) = (1, i + 1, true) := by
            simp [mapStep, hi1, hi2]
          rw [this, mapStep_stop]
          rcases gsCompare_range k k' with h | h | h
          · exact absurd ((gsLt_iff k k').2 h) hlt
          · exact absurd h hne
          · exact h.symm

theorem compareF_map (n : Nat) (xs ys : List (GoString × UVal)) :
    UVal.compareF (n + 1) (.map xs) (.map ys) = listCmp (pairCmp (UVal.compareF n)) xs ys := by
  rw [compareF_map_raw]
  by_cases h : xs.length == 0 && ys.length == 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
    simp only [Bool.and_eq_true, beq_iff_eq, List.length_eq_zero_iff] at h
    rw [h.1, h.2]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
    exact mapFold_eq _ _ _ _ xs ys 0 (by omega) (by omega) (by omega)

/-! ## Sizes -/

theorem size_pos (a : UVal) : 1 ≤ a.size := by
  cases a <;> simp [UVal.size]

theorem mem_sizeL {x : UVal} : ∀ {xs : List UVal}, x ∈ xs → x.size ≤ UVal.sizeL xs
  | [], h => by simp at h
  | y :: ys, h => by
      simp only [UVal.sizeL]
      rcases List.mem_cons.1 h with h | h
      · subst h; omega
      · have := mem_sizeL h; omega

theorem mem_sizeM {p : GoString × UVal} : ∀ {kvs : List (GoString × UVal)}, p ∈ kvs →
    p.2.size ≤ UVal.sizeM kvs
  | [], h => by simp at h
  | (k, v) :: kvs, h => by
      simp only [UVal.sizeM]
      rcases List.mem_cons.1 h with h | h
      · subst h; simp
      · have := mem_sizeM h; omega

theorem pairCmp_congr (f g : UVal → UVal → Int) (p q : GoString × UVal) (h : f p.2 q.2 = g p.2 q.2) :
    pairCmp f p q = pairCmp g p q := by
  simp only [pairCmp, h]

/-! ## The fuel lemma -/

theorem compareF_fuel_eq : ∀ (n m : Nat) (a b : UVal), a.size + b.size < n → a.size + b.size < m →
    UVal.compareF n a b = UVal.compareF m a b
  | 0, _, _, _, h, _ => by omega
  | _ + 1, 0, _, _, _, h => by omega
  | n + 1, m + 1, a, b, hn, hm => by
      cases a <;> cases b
      all_goals first
        | rfl
        | (rename_i xs ys
           simp only [UVal.size] at hn hm
           first
           | (rw [compareF_list, compareF_list]
              apply listCmp_congr
              intro x hx y hy
              have := mem_sizeL hx; have := mem_sizeL hy
              exact compareF_fuel_eq n m x y (by omega) (by omega))
           | (rw [compareF_map, compareF_map]
              apply listCmp_congr
              intro x hx y hy
              apply pairCmp_congr
              have := mem_sizeM hx; have := mem_sizeM hy
              exact compareF_fuel_eq n m x.2 y.2 (by omega) (by omega)))

/-- **The fuel lemma**: any fuel above `a.size + b.size` gives `UVal.compare a b`. -/
theorem _root_.Perennial.EtcdGrove.smd.UVal.compareF_fuel : ∀ (n : Nat) (a b : UVal),
    a.size + b.size + 1 ≤ n → UVal.compareF n a b = UVal.compare a b := by
  intro n a b h
  exact compareF_fuel_eq n _ a b (by omega) (by omega)

theorem compare_list (xs ys : List UVal) :
    UVal.compare (.list xs) (.list ys) = listCmp UVal.compare xs ys := by
  simp only [UVal.compare, UVal.size]
  rw [show UVal.sizeL xs + 1 + (UVal.sizeL ys + 1) + 1 = (UVal.sizeL xs + UVal.sizeL ys + 2) + 1 by omega,
    compareF_list]
  apply listCmp_congr
  intro x hx y hy
  have := mem_sizeL hx; have := mem_sizeL hy
  exact UVal.compareF_fuel _ x y (by omega)

theorem compare_map (xs ys : List (GoString × UVal)) :
    UVal.compare (.map xs) (.map ys) = listCmp (pairCmp UVal.compare) xs ys := by
  simp only [UVal.compare, UVal.size]
  rw [show UVal.sizeM xs + 1 + (UVal.sizeM ys + 1) + 1 = (UVal.sizeM xs + UVal.sizeM ys + 2) + 1 by omega,
    compareF_map]
  apply listCmp_congr
  intro x hx y hy
  apply pairCmp_congr
  have := mem_sizeM hx; have := mem_sizeM hy
  exact UVal.compareF_fuel _ x.2 y.2 (by omega)

/-! ## Generic lexicographic facts -/

/-- `c` is `-1`, `0` or `1`. -/
def Rng (c : Int) : Prop := c = -1 ∨ c = 0 ∨ c = 1

theorem listCmp_range {α : Type} (f : α → α → Int) : ∀ (xs ys : List α),
    (∀ x ∈ xs, ∀ y, Rng (f x y)) → Rng (listCmp f xs ys)
  | [], [], _ => by simp [listCmp, Rng]
  | [], _ :: _, _ => by simp [listCmp, Rng]
  | _ :: _, [], _ => by simp [listCmp, Rng]
  | x :: xs, y :: ys, h => by
      simp only [listCmp]
      split
      · exact listCmp_range f xs ys (fun a ha b => h a (by simp [ha]) b)
      · exact h x (by simp) y

theorem listCmp_swap {α : Type} (f : α → α → Int) : ∀ (xs ys : List α),
    (∀ x ∈ xs, ∀ y, f y x = - f x y) → listCmp f ys xs = - listCmp f xs ys
  | [], [], _ => by simp [listCmp]
  | [], _ :: _, _ => by simp [listCmp]
  | _ :: _, [], _ => by simp [listCmp]
  | x :: xs, y :: ys, h => by
      simp only [listCmp]
      rw [h x (by simp) y, listCmp_swap f xs ys (fun a ha b => h a (by simp [ha]) b)]
      by_cases hc : f x y = 0 <;> simp [hc]

theorem listCmp_eq {α : Type} (f : α → α → Int) : ∀ (xs ys : List α),
    (∀ x ∈ xs, ∀ y, f x y = 0 → x = y) → listCmp f xs ys = 0 → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [listCmp] at h
  | _ :: _, [], _, h => by simp [listCmp] at h
  | x :: xs, y :: ys, hf, h => by
      simp only [listCmp] at h
      by_cases hc : f x y = 0
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h
        rw [hf x (by simp) y hc, listCmp_eq f xs ys (fun a ha b => hf a (by simp [ha]) b) h]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; exact absurd h hc

theorem listCmp_trans {α : Type} (f : α → α → Int) (heq : ∀ x y, f x y = 0 → x = y)
    (hrefl : ∀ x, f x x = 0) : ∀ (xs ys zs : List α),
    (∀ x ∈ xs, ∀ y z, f x y = -1 → f y z = -1 → f x z = -1) →
    listCmp f xs ys = -1 → listCmp f ys zs = -1 → listCmp f xs zs = -1
  | [], [], _, _, h, _ => by simp [listCmp] at h
  | _ :: _, [], _, _, h, _ => by simp [listCmp] at h
  | _, _ :: _, [], _, _, h => by simp [listCmp] at h
  | [], _ :: _, _ :: _, _, _, _ => rfl
  | x :: xs, y :: ys, z :: zs, ht, h1, h2 => by
      simp only [listCmp] at h1 h2 ⊢
      by_cases c1 : f x y = 0
      · rw [ite_eq_left_of_eq_true _ _ (eq_true c1)] at h1
        have := heq x y c1; subst this
        by_cases c2 : f x z = 0
        · rw [ite_eq_left_of_eq_true _ _ (eq_true c2)] at h2 ⊢
          exact listCmp_trans f heq hrefl xs ys zs (fun a ha b c => ht a (by simp [ha]) b c) h1 h2
        · rw [ite_eq_right_of_eq_false _ _ (eq_false c2)] at h2 ⊢; exact h2
      · rw [ite_eq_right_of_eq_false _ _ (eq_false c1)] at h1
        by_cases c2 : f y z = 0
        · have := heq y z c2; subst this
          rw [ite_eq_right_of_eq_false _ _ (eq_false c1)]; exact h1
        · rw [ite_eq_right_of_eq_false _ _ (eq_false c2)] at h2
          have := ht x (by simp) y z h1 h2
          rw [this]; simp

/-! ## Entry comparison -/

theorem pairCmp_range (f : UVal → UVal → Int) (p q : GoString × UVal) (h : Rng (f p.2 q.2)) :
    Rng (pairCmp f p q) := by
  unfold pairCmp; split
  · exact h
  · exact gsCompare_range _ _

theorem pairCmp_swap (f : UVal → UVal → Int) (p q : GoString × UVal) (h : f q.2 p.2 = - f p.2 q.2) :
    pairCmp f q p = - pairCmp f p q := by
  unfold pairCmp
  rw [gsCompare_swap p.1 q.1]
  by_cases hc : gsCompare p.1 q.1 = 0
  · simp [hc, h]
  · have : ¬ -gsCompare p.1 q.1 = 0 := by omega
    simp [hc, this]

theorem pairCmp_eq (f : UVal → UVal → Int) (p q : GoString × UVal) (h : f p.2 q.2 = 0 → p.2 = q.2) :
    pairCmp f p q = 0 → p = q := by
  unfold pairCmp
  by_cases hc : gsCompare p.1 q.1 = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]; intro h0
    have h1 := gsCompare_eq_zero _ _ hc
    have h2 := h h0
    cases p; cases q; simp_all
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]; intro h0; exact absurd h0 hc

theorem pairCmp_refl (f : UVal → UVal → Int) (p : GoString × UVal) (h : f p.2 p.2 = 0) :
    pairCmp f p p = 0 := by
  simp [pairCmp, gsCompare_self, h]

theorem pairCmp_trans (f : UVal → UVal → Int) (p q r : GoString × UVal)
    (h : f p.2 q.2 = -1 → f q.2 r.2 = -1 → f p.2 r.2 = -1) :
    pairCmp f p q = -1 → pairCmp f q r = -1 → pairCmp f p r = -1 := by
  unfold pairCmp
  intro h1 h2
  by_cases c1 : gsCompare p.1 q.1 = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true c1)] at h1
    have e1 := gsCompare_eq_zero _ _ c1
    rw [e1]
    by_cases c2 : gsCompare q.1 r.1 = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true c2)] at h2 ⊢; exact h h1 h2
    · rw [ite_eq_right_of_eq_false _ _ (eq_false c2)] at h2 ⊢; exact h2
  · rw [ite_eq_right_of_eq_false _ _ (eq_false c1)] at h1
    by_cases c2 : gsCompare q.1 r.1 = 0
    · have e2 := gsCompare_eq_zero _ _ c2
      rw [← e2, ite_eq_right_of_eq_false _ _ (eq_false c1)]; exact h1
    · rw [ite_eq_right_of_eq_false _ _ (eq_false c2)] at h2
      have := gsCompare_trans _ _ _ h1 h2
      rw [this]; simp

/-! ## Scalars -/

theorem intCompare_range (x y : w64) : Rng (intCompare x y) := by
  unfold intCompare Rng
  by_cases h1 : x.toInt > y.toInt <;> by_cases h2 : x.toInt = y.toInt <;> simp [h1, h2]

set_option linter.unusedSimpArgs false in
theorem intCompare_swap (x y : w64) : intCompare y x = - intCompare x y := by
  unfold intCompare
  by_cases h1 : x.toInt < y.toInt <;> by_cases h2 : y.toInt < x.toInt <;>
    by_cases h3 : x.toInt = y.toInt <;> simp [h1, h2, h3] <;> omega

theorem intCompare_eq (x y : w64) : intCompare x y = 0 → x = y := by
  unfold intCompare
  by_cases h1 : x.toInt > y.toInt <;> by_cases h2 : x.toInt = y.toInt <;> simp [h1, h2] <;> exact BitVec.eq_of_toInt_eq h2

set_option linter.unusedSimpArgs false in
theorem intCompare_trans (x y z : w64) : intCompare x y = -1 → intCompare y z = -1 →
    intCompare x z = -1 := by
  unfold intCompare
  by_cases h1 : x.toInt < y.toInt <;> by_cases h2 : y.toInt < z.toInt <;>
    by_cases h3 : x.toInt < z.toInt <;> by_cases h4 : x.toInt = y.toInt <;>
    by_cases h5 : y.toInt = z.toInt <;> by_cases h6 : x.toInt = z.toInt <;>
    simp [h1, h2, h3, h4, h5, h6] <;> omega

theorem boolCompare_range (x y : Bool) : Rng (boolCompare x y) := by
  cases x <;> cases y <;> simp [boolCompare, Rng]

theorem boolCompare_swap (x y : Bool) : boolCompare y x = - boolCompare x y := by
  cases x <;> cases y <;> simp [boolCompare]

theorem boolCompare_eq (x y : Bool) : boolCompare x y = 0 → x = y := by
  cases x <;> cases y <;> simp [boolCompare]

theorem boolCompare_trans (x y z : Bool) : boolCompare x y = -1 → boolCompare y z = -1 →
    boolCompare x z = -1 := by
  cases x <;> cases y <;> cases z <;> simp [boolCompare]

/-! ## Kinds -/

/-- The rank of a value's kind in `value.Compare`'s order. -/
def tag : UVal → Nat
  | .int _ => 0
  | .str _ => 1
  | .bool _ => 2
  | .list _ => 3
  | .map _ => 4
  | .null => 5

theorem compare_tag {a b : UVal} (h : tag a ≠ tag b) :
    UVal.compare a b = if tag a < tag b then -1 else 1 := by
  cases a <;> cases b <;> first | exact absurd rfl h | rfl

theorem compare_int (x y : w64) : UVal.compare (.int x) (.int y) = intCompare x y := rfl
theorem compare_str (x y : GoString) : UVal.compare (.str x) (.str y) = gsCompare x y := rfl
theorem compare_bool (x y : Bool) : UVal.compare (.bool x) (.bool y) = boolCompare x y := rfl
theorem compare_null : UVal.compare .null .null = 0 := rfl

/-! ## The order -/

theorem compare_props : ∀ (n : Nat) (a : UVal), a.size < n → ∀ b,
    Rng (UVal.compare a b) ∧ UVal.compare b a = - UVal.compare a b ∧ (UVal.compare a b = 0 → a = b)
  | 0, a, h, _ => absurd h (by have := size_pos a; omega)
  | n + 1, a, h, b => by
    by_cases ht : tag a = tag b
    · cases a <;> cases b <;> simp [tag] at ht
      · simp [compare_null, Rng]
      · rename_i x y
        rw [compare_bool, compare_bool]
        exact ⟨boolCompare_range x y, boolCompare_swap x y,
          fun h0 => by rw [boolCompare_eq x y h0]⟩
      · rename_i x y
        rw [compare_int, compare_int]
        exact ⟨intCompare_range x y, intCompare_swap x y,
          fun h0 => by rw [intCompare_eq x y h0]⟩
      · rename_i x y
        rw [compare_str, compare_str]
        exact ⟨gsCompare_range x y, gsCompare_swap x y,
          fun h0 => by rw [gsCompare_eq_zero x y h0]⟩
      · rename_i xs ys
        simp only [UVal.size] at h
        have ih : ∀ x ∈ xs, ∀ y, _ := fun x hx y =>
          compare_props n x (by have := mem_sizeL hx; omega) y
        rw [compare_list, compare_list]
        exact ⟨listCmp_range _ _ _ (fun x hx y => (ih x hx y).1),
          listCmp_swap _ _ _ (fun x hx y => (ih x hx y).2.1),
          fun h0 => by rw [listCmp_eq _ _ _ (fun x hx y => (ih x hx y).2.2) h0]⟩
      · rename_i xs ys
        simp only [UVal.size] at h
        have ih : ∀ p ∈ xs, ∀ y, _ := fun p hp y =>
          compare_props n p.2 (by have := mem_sizeM hp; omega) y
        rw [compare_map, compare_map]
        exact ⟨listCmp_range _ _ _ (fun p hp q => pairCmp_range _ p q (ih p hp q.2).1),
          listCmp_swap _ _ _ (fun p hp q => pairCmp_swap _ p q (ih p hp q.2).2.1),
          fun h0 => by
            rw [listCmp_eq _ _ _ (fun p hp q => pairCmp_eq _ p q (ih p hp q.2).2.2) h0]⟩
    · rw [compare_tag ht, compare_tag (Ne.symm ht)]
      refine ⟨?_, ?_, ?_⟩
      · unfold Rng; split <;> simp
      · by_cases hl : tag a < tag b
        · have : ¬ tag b < tag a := by omega
          simp [hl, this]
        · have : tag b < tag a := by omega
          simp [hl, this]
      · intro h0; split at h0 <;> simp at h0

theorem compare_rng (a b : UVal) : Rng (UVal.compare a b) :=
  (compare_props _ a (Nat.lt_succ_self _) b).1

theorem compare_swap (a b : UVal) : UVal.compare b a = - UVal.compare a b :=
  (compare_props _ a (Nat.lt_succ_self _) b).2.1

theorem compare_eq (a b : UVal) : UVal.compare a b = 0 → a = b :=
  (compare_props _ a (Nat.lt_succ_self _) b).2.2

theorem compare_self (a : UVal) : UVal.compare a a = 0 := by
  have := compare_swap a a; omega

theorem compare_neg_tag {a b : UVal} (h : UVal.compare a b = -1) : tag a ≤ tag b := by
  by_cases ht : tag a = tag b
  · omega
  · rw [compare_tag ht] at h
    split at h
    · omega
    · simp at h

theorem compare_trans' : ∀ (n : Nat) (a : UVal), a.size < n → ∀ b c,
    UVal.compare a b = -1 → UVal.compare b c = -1 → UVal.compare a c = -1
  | 0, a, h, _, _, _, _ => absurd h (by have := size_pos a; omega)
  | n + 1, a, h, b, c, h1, h2 => by
    have t1 := compare_neg_tag h1
    have t2 := compare_neg_tag h2
    by_cases hac : tag a = tag c
    · have hab : tag a = tag b := by omega
      have hbc : tag b = tag c := by omega
      clear hac t1 t2
      cases a <;> cases b <;> simp [tag] at hab <;> cases c <;> simp [tag] at hbc
      · simp [compare_null] at h1
      · rename_i x y z
        rw [compare_bool] at *; exact boolCompare_trans x y z h1 h2
      · rename_i x y z
        rw [compare_int] at *; exact intCompare_trans x y z h1 h2
      · rename_i x y z
        rw [compare_str] at *; exact gsCompare_trans x y z h1 h2
      · rename_i xs ys zs
        simp only [UVal.size] at h
        rw [compare_list] at *
        exact listCmp_trans _ compare_eq compare_self xs ys zs
          (fun x hx y z => compare_trans' n x (by have := mem_sizeL hx; omega) y z) h1 h2
      · rename_i xs ys zs
        simp only [UVal.size] at h
        rw [compare_map] at *
        exact listCmp_trans _ (fun p q => pairCmp_eq _ p q (compare_eq p.2 q.2))
          (fun p => pairCmp_refl _ p (compare_self p.2)) xs ys zs
          (fun p hp q r => pairCmp_trans _ p q r
            (compare_trans' n p.2 (by have := mem_sizeM hp; omega) q.2 r.2)) h1 h2
    · rw [compare_tag hac]
      have : tag a < tag c := by omega
      simp [this]

end ValueCompare

open ValueCompare

/-- `UVal.compare`'s results are `-1`, `0`, `1`. -/
theorem UVal.compare_range (a b : UVal) :
    UVal.compare a b = -1 ∨ UVal.compare a b = 0 ∨ UVal.compare a b = 1 :=
  compare_rng a b

theorem UVal.compare_eq_zero_law_holds : UVal.compare_eq_zero.law := by
  intro a b _ _
  exact ⟨compare_eq a b, fun h => h ▸ compare_self a⟩

theorem UVal.compare_antisymm_law_holds : UVal.compare_antisymm.law := by
  intro a b _ _
  rw [compare_swap a b]; omega

theorem UVal.compare_trans_law_holds : UVal.compare_trans.law := by
  intro a b c _ _ _ h1 h2
  have r1 := compare_rng a b
  have r2 := compare_rng b c
  have r3 := compare_rng a c
  unfold Rng at r1 r2 r3
  have := compare_trans' _ a (Nat.lt_succ_self _) b c (by omega) (by omega)
  omega

end smd
end EtcdGrove
end Perennial
