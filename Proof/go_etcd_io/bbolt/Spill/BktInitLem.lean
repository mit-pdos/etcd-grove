/-
`Bucket.spill`'s initial trees (U9i, `notes/bbolt-proof-plan.md`), part 3: helpers of
`Spill/BktInit` (pure): the parent chain of a bucket's nodes (`upTo`, linear), the bounds of an
entry's child (`wEntryBnd_eq`), the walk's fuel by page heights (`leavesF_pht`), and the
distinctness of a `filterMap` (`filterMap_nodup_of`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTree
public import Proof.go_etcd_io.bbolt.Spill.BktEls

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section lem
variable [GooseExts]

/-- Node `x` of `B` reaches `y` following `parent`. -/
inductive upTo (B : BRec) : Loc → Loc → Prop
  | refl (x : Loc) : upTo B x x
  | up (x y : Loc) (r : NRec) : B.ns !! x = some r → r.nv.parent' ≠ null →
      upTo B r.nv.parent' y → upTo B x y

/-- The parent chain is linear. -/
theorem upTo_lin {B : BRec} {x a b : Loc} (ha : upTo B x a) (hb : upTo B x b) :
    upTo B a b ∨ upTo B b a := by
  induction ha generalizing b with
  | refl x => exact Or.inl hb
  | up x y r hr hp _ ih =>
    cases hb with
    | refl => exact Or.inr (upTo.up _ _ r hr hp ‹_›)
    | up _ _ r' hr' _ hb' =>
      rw [hr] at hr'; cases hr'
      exact ih hb'

/-- Along the parent chain the heights grow (`ht x + 1 = ht parent`). -/
theorem upTo_ht {B : BRec} {ht : Loc → Nat}
    (hpar : ∀ x r, B.ns !! x = some r → r.nv.parent' ≠ null → ht x + 1 = ht r.nv.parent')
    {x y : Loc} (h : upTo B x y) : x = y ∨ ht x < ht y := by
  induction h with
  | refl => exact Or.inl rfl
  | up x y r hr hp _ ih =>
    have := hpar x r hr hp
    rcases ih with e | lt
    · right; rw [← e]; omega
    · right; omega

theorem wKey_eq (ws : List WEntry) : (fun j => (ws.map WEntry.key).getD j []) = wKey ws := by
  funext j
  unfold wKey
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]

/-- The bounds of entry `i`'s child, as `uTree` writes them. -/
theorem wEntryBnd_eq (b : Option (List w8) × Option (List w8)) (ws : List WEntry) (i : Nat) :
    wEntryBnd b ws i = (childLo b.1 (wKey ws) i, childHi b.2 (wKey ws) ws.length i) := by
  unfold wEntryBnd entryBnd
  rw [wKey_eq, List.length_map]

/-- **The walk's fuel by page heights**: any fuel above the page's height walks the same leaves. -/
theorem leavesF_pht (P : Pages) (hwm : Nat) (pht : Nat → Nat) (hht : pageHts P pht) :
    ∀ n m id, treeWF P hwm id → pht id < n → pht id < m → leavesF n P id = leavesF m P id
  | 0, _, _, _, h1, _ => absurd h1 (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _, h2 => absurd h2 (Nat.not_lt_zero _)
  | n + 1, m + 1, id, hw, h1, h2 => by
    cases hw with
    | page _ pg _ _ hpg _ _ hpt =>
    simp only [leavesF, hpg]
    by_cases hl : pageFlags pg = leafPageFlag
    · simp [hl]
    · simp only [hl, ite_false]
      cases hpt with
      | leaf _ _ hfl => exact absurd hfl hl
      | branch _ _ hfl _ hch =>
        have hh := (hht id pg hpg).2 hfl
        apply flatMap_congr_els
        intro i hi
        have hi' := List.mem_range.1 hi
        have := hh i hi'
        exact leavesF_pht P hwm pht hht n m _ (hch i hi') (by omega) (by omega)

/-- A `filterMap` whose distinct positions give distinct values is distinct. -/
theorem filterMap_nodup_of {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ (i j : Nat) x y b, i < j → l[i]? = some x → l[j]? = some y → f x = some b →
      f y ≠ some b) → (l.filterMap f).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    have ht : (l.filterMap f).Nodup := filterMap_nodup_of f l (fun i j x y b hij hx hy hfx =>
      h (i + 1) (j + 1) x y b (by omega) (by simpa using hx) (by simpa using hy) hfx)
    rw [List.filterMap_cons]
    cases hfa : f a with
    | none => exact ht
    | some b =>
      refine List.nodup_cons.2 ⟨?_, ht⟩
      intro hm
      obtain ⟨y, hy, hfy⟩ := List.mem_filterMap.1 hm
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
      exact h 0 (j + 1) a _ b (by omega) rfl (by simp [hj]) hfa hfy

/-- A distinct list's positions of one value are one. -/
theorem nodup_idx {α : Type} : ∀ {l : List α} {i j : Nat} {a : α}, l.Nodup → l[i]? = some a →
    l[j]? = some a → i = j
  | [], _, _, _, _, h, _ => by simp at h
  | b :: l, 0, 0, _, _, _, _ => rfl
  | b :: l, 0, j + 1, a, hn, hi, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    simp only [List.getElem?_cons_succ] at hj
    exact absurd (List.mem_of_getElem? hj) (List.nodup_cons.1 hn).1
  | b :: l, i + 1, 0, a, hn, hi, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    simp only [List.getElem?_cons_succ] at hi
    exact absurd (List.mem_of_getElem? hi) (List.nodup_cons.1 hn).1
  | b :: l, i + 1, j + 1, a, hn, hi, hj => by
    simp only [List.getElem?_cons_succ] at hi hj
    rw [nodup_idx (List.nodup_cons.1 hn).2 hi hj]

/-- A `flatMap` of distinct lists, disjoint at distinct positions, is distinct. -/
theorem nodup_flatMap_of {α β : Type} (f : α → List β) :
    ∀ (l : List α), (∀ a ∈ l, (f a).Nodup) →
      (∀ (i j : Nat) a b x, i < j → l[i]? = some a → l[j]? = some b → x ∈ f a → x ∉ f b) →
      (l.flatMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h1, h2 => by
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨h1 a List.mem_cons_self, nodup_flatMap_of f l (fun b hb => h1 b
      (List.mem_cons_of_mem _ hb)) (fun i j x y z hij hx hy => h2 (i + 1) (j + 1) x y z (by omega)
      (by simpa using hx) (by simpa using hy)), ?_⟩
    intro x hx y hy hxy
    subst hxy
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.1 hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    exact h2 0 (j + 1) a _ x (by omega) rfl (by simp [hj]) hx hxb

/-- `flatMap`s of lists with the same images. -/
theorem flatMap_of_map_eq {α γ β : Type} {l1 : List α} {l2 : List γ} {f : α → List β}
    {g : γ → List β} (h : l1.map f = l2.map g) : l1.flatMap f = l2.flatMap g := by
  rw [List.flatMap_def, List.flatMap_def, h]

/-- The parent chain is transitive. -/
theorem upTo_trans {B : BRec} {x y z : Loc} (h1 : upTo B x y) (h2 : upTo B y z) : upTo B x z := by
  induction h1 with
  | refl => exact h2
  | up x y r hr hp _ ih => exact upTo.up x z r hr hp (ih h2)

end lem

end Spill

end bbolt
end EtcdGrove
end Perennial
