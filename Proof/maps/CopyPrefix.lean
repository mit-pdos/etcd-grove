/-
`maps.copyPrefix S D l`: `S`'s entries at the keys of `l`, over `D` -- the state of a map that a loop
over `S`'s keys in the order `l` copies into (`maps.Copy`'s proof; `featureGate.Add`'s, whose loop
inserts `features` into a copy of the known features). Pure.
-/
module

public import Perennial.Std.GMap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- `src`'s entries at the keys of `l`, over `D`. -/
def maps.copyPrefix {K V : Type} [DecidableEq K] (S D : GMap K V) (l : List K) : GMap K V :=
  GMap.filter (fun k _ => decide (k ∈ l)) S ∪ D

theorem maps.copyPrefix_nil {K V : Type} [DecidableEq K] (S D : GMap K V) :
    maps.copyPrefix S D [] = D := by
  apply GMap.map_eq; intro k
  simp [maps.copyPrefix]

theorem maps.copyPrefix_snoc {K V : Type} [DecidableEq K] (S D : GMap K V) (l : List K) (key : K)
    (v : V) (h : S !! key = some v) :
    <[key := v]> (maps.copyPrefix S D l) = maps.copyPrefix S D (l ++ [key]) := by
  apply GMap.map_eq; intro k
  by_cases hk : key = k
  · subst hk
    rw [GMap.lookup_insert]
    simp [maps.copyPrefix, h, Option.filter]
  · rw [GMap.lookup_insert_ne _ _ hk]
    have hk' : k ≠ key := fun e => hk e.symm
    simp [maps.copyPrefix, hk']

theorem maps.copyPrefix_all {K V : Type} [DecidableEq K] (S D : GMap K V) (l : List K)
    (h : ∀ k, k ∈ l ↔ (S !! k).isSome) :
    maps.copyPrefix S D l = S ∪ D := by
  apply GMap.map_eq; intro k
  simp only [maps.copyPrefix, GMap.lookup_union, GMap.lookup_filter]
  cases hs : S !! k with
  | none => rfl
  | some v =>
    have : k ∈ l := (h k).2 (by rw [hs]; rfl)
    simp [this]

theorem maps.copyPrefix_lookup_notin {K V : Type} [DecidableEq K] (S D : GMap K V) (l : List K)
    (k : K) (h : k ∉ l) : maps.copyPrefix S D l !! k = D !! k := by
  simp [maps.copyPrefix, h, Option.filter]
  cases S !! k <;> rfl

/-- At a key already holding `S`'s value, the step leaves the map as it is. -/
theorem maps.copyPrefix_snoc_same {K V : Type} [DecidableEq K] (S D : GMap K V) (l : List K)
    (key : K) (v : V) (h : S !! key = some v) (h' : maps.copyPrefix S D l !! key = some v) :
    maps.copyPrefix S D l = maps.copyPrefix S D (l ++ [key]) := by
  rw [← maps.copyPrefix_snoc S D l key v h, GMap.insert_id _ _ _ h']

/-- The `i`-th key of a duplicate-free list is not among the first `i`. -/
theorem maps.nodup_getElem_notin_take {K : Type} (keys : List K) (i : Nat) (key : K)
    (hnd : keys.Nodup) (hk : keys[i]? = some key) : key ∉ keys.take i := by
  intro hm
  obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hm
  have hji : j < i := by simp at hj; omega
  have hjl : j < keys.length := by simp at hj; omega
  have hil : i < keys.length := by
    rcases Nat.lt_or_ge i keys.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hk; cases hk
  have hjk' : keys[j] = key := by rw [← hjk, List.getElem_take]
  have hik : keys[i] = key := by
    rw [List.getElem?_eq_getElem hil] at hk; exact Option.some.inj hk
  have := hnd.eq_of_getElem_eq hjl hil (hjk'.trans hik.symm)
  omega

end EtcdGrove
end Perennial
