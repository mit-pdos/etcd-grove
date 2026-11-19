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
  · rw [if_pos h]
    simp only [Bool.and_eq_true, beq_iff_eq, List.length_eq_zero_iff] at h
    rw [h.1, h.2]; rfl
  · rw [if_neg h]
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

end ValueCompare

end smd
end EtcdGrove
end Perennial
