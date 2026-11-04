/-
**The view facts behind the page tokens' moves** (batch 37 item 14; `Inv/ShapeOps`): what a
position's tokens (`xPages`) decompose into when its page is materialized (`xPages_page_sub`: the
page itself and its children's subtrees, or its nested buckets' trees), from the view's
uniqueness (`viewUnique`: no page shared). Pure.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.ShapeOps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section view
variable [GooseExts]

open Classical

/-- `xHas` reaches only pages of the tree. -/
theorem xHas_treeHas {P : Pages} {op : List w8 → Prop} {c id : Nat} (h : xHas P op c id) :
    treeHas P c id := by
  induction h with
  | root root pg hpg => exact treeHas.root root pg hpg
  | child root pg i id hpg hfl hi _ ih => exact treeHas.sub root pg id hpg (pageHas.child pg i id hfl hi ih)
  | bucket root pg i id hpg hfl hi hb _ hbh =>
    exact treeHas.sub root pg id hpg (pageHas.bucket pg i id hfl hi hb hbh)

/-- Excluding more buckets reaches fewer pages. -/
theorem xHas_mono {P : Pages} {op op' : List w8 → Prop} (hop : ∀ k, op k → op' k) {c id : Nat}
    (h : xHas P op' c id) : xHas P op c id := by
  induction h with
  | root root pg hpg => exact xHas.root root pg hpg
  | child root pg i id hpg hfl hi _ ih => exact xHas.child root pg i id hpg hfl hi ih
  | bucket root pg i id hpg hfl hi hb hno hbh =>
    exact xHas.bucket root pg i id hpg hfl hi hb (fun h => hno (hop _ h)) hbh

/-- A page of a tree is a page of the map. -/
theorem treeHas_some {P : Pages} {r y : Nat} (h : treeHas P r y) : (P !! y).isSome :=
  treeHas.rec (pages := P)
    (motive_1 := fun _ y _ => (P !! y).isSome)
    (motive_2 := fun _ y _ => (P !! y).isSome)
    (motive_3 := fun _ y _ => (P !! y).isSome)
    (fun _ pg hpg => by rw [hpg]; rfl) (fun _ _ _ _ _ ih => ih) (fun _ _ _ _ _ _ ih => ih)
    (fun _ _ _ _ _ _ _ ih => ih) (fun _ _ _ _ ih => ih) (fun _ _ _ _ ih => ih) h

theorem mem_filter_pgIds {P : Pages} {q : Nat → Bool} {id : Nat} :
    id ∈ pgIds (GMap.filter (fun id _ => q id) P) ↔ (P !! id).isSome ∧ q id = true := by
  rw [mem_pgIds, GMap.lookup_filter]
  cases e : P !! id with
  | none => simp [Option.filter]
  | some pg => cases hq : q id <;> simp [Option.filter, hq]

theorem mem_xPages {P : Pages} {op : List w8 → Prop} {c id : Nat} :
    id ∈ pgIds (xPages P op c) ↔ xHas P op c id := by
  unfold xPages; rw [mem_filter_pgIds]
  exact ⟨fun h => of_decide_eq_true h.2, fun h => ⟨treeHas_some (xHas_treeHas h), decide_eq_true h⟩⟩

theorem mem_treePages {P : Pages} {c id : Nat} :
    id ∈ pgIds (treePages P c) ↔ treeHas P c id := by
  unfold treePages; rw [mem_filter_pgIds]
  exact ⟨fun h => of_decide_eq_true h.2, fun h => ⟨treeHas_some h, decide_eq_true h⟩⟩

theorem pairwise_range_of_ne {R : Nat → Nat → Prop} {n : Nat}
    (h : ∀ i j, i < n → j < n → i ≠ j → R i j) : (List.range n).Pairwise R :=
  (List.nodup_range).imp_of_mem fun hi hj hne =>
    h _ _ (List.mem_range.1 hi) (List.mem_range.1 hj) hne

/-- A position's own page: at most the page `p`. -/
def ownAt (own : List Nat) (p : Nat) : Prop := own.Nodup ∧ ∀ x ∈ own, x = p

/-- **A leaf page's decomposition**: its own page and the trees of its nested buckets stored in
pages and not opened (`op`) are the position's pages, without duplicate (`viewUnique`). Each
entry `i` owns either nothing or its bucket's tree (`f i`). -/
theorem xPages_leaf_sub (P : Pages) (op : List w8 → Prop) (p : Nat) (pg : List w8)
    (hu : viewUnique P) (hpg : P !! p = some pg) (hfl : pageFlags pg = leafPageFlag)
    (own : List Nat) (hown : ownAt own p) (f : Nat → List Nat)
    (hf : ∀ i < pageCount pg, f i = [] ∨ (leafFlags pg i % 2 = bucketLeafFlag ∧
      inBucketRoot (leafValue pg i) ≠ 0 ∧ ¬ op (leafKey pg i) ∧
      f i = pgIds (treePages P (inBucketRoot (leafValue pg i))))) :
    (own ++ (List.range (pageCount pg)).flatMap f).Subperm (pgIds (xPages P op p)) := by
  have hu2 := hu.2 p pg hpg hfl
  -- an id of entry `i`'s list is a page of its bucket's tree
  have hmem : ∀ i < pageCount pg, ∀ x ∈ f i, leafFlags pg i % 2 = bucketLeafFlag ∧
      ¬ op (leafKey pg i) ∧ bucketHas P (leafValue pg i) x := by
    intro i hi x hx
    rcases hf i hi with e | ⟨hb, hr, hno, e⟩
    · rw [e] at hx; cases hx
    · rw [e, mem_treePages] at hx
      exact ⟨hb, hno, bucketHas.file _ _ hr hx⟩
  refine List.subperm_of_subset ?_ ?_
  · rw [List.nodup_append]
    refine ⟨hown.1, ?_, ?_⟩
    · unfold List.Nodup
      rw [List.pairwise_flatMap]
      refine ⟨fun i hi => ?_, pairwise_range_of_ne fun i j hi hj hne x hx y hy => ?_⟩
      · have hi := List.mem_range.1 hi
        rcases hf i hi with e | ⟨-, -, -, e⟩
        · rw [e]; exact List.nodup_nil
        · rw [e]; exact pgIds_nodup _
      · obtain ⟨hbi, -, hxi⟩ := hmem i hi x hx
        obtain ⟨hbj, -, hyj⟩ := hmem j hj y hy
        rintro rfl
        exact hu2.1 i j hi hj hne hbi hbj x hxi hyj
    · intro a ha b hb
      rw [hown.2 a ha]
      obtain ⟨i, hi, hbi⟩ := List.mem_flatMap.1 hb
      have hi := List.mem_range.1 hi
      obtain ⟨hb1, -, hbh⟩ := hmem i hi b hbi
      rintro rfl
      exact hu2.2 i hi hb1 hbh
  · intro x hx
    rw [mem_xPages]
    rcases List.mem_append.1 hx with hx | hx
    · rw [hown.2 x hx]; exact xHas.root p pg hpg
    · obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.1 hx
      have hi := List.mem_range.1 hi
      obtain ⟨hb1, hno, hbh⟩ := hmem i hi x hxi
      exact xHas.bucket p pg i x hpg hfl hi hb1 hno hbh

/-- **A branch page's decomposition**: its own page and its children's positions (those not
materialized: `f i`) are the position's pages, without duplicate (`viewUnique`). -/
theorem xPages_branch_sub (P : Pages) (op : List w8 → Prop) (p : Nat) (pg : List w8)
    (hu : viewUnique P) (hpg : P !! p = some pg) (hfl : pageFlags pg = branchPageFlag)
    (own : List Nat) (hown : ownAt own p) (f : Nat → List Nat)
    (hf : ∀ i < pageCount pg, f i = [] ∨ f i = pgIds (xPages P op (branchPgid pg i))) :
    (own ++ (List.range (pageCount pg)).flatMap f).Subperm (pgIds (xPages P op p)) := by
  have hu1 := hu.1 p pg hpg hfl
  have hmem : ∀ i < pageCount pg, ∀ x ∈ f i, xHas P op (branchPgid pg i) x := by
    intro i hi x hx
    rcases hf i hi with e | e
    · rw [e] at hx; cases hx
    · rw [e, mem_xPages] at hx; exact hx
  refine List.subperm_of_subset ?_ ?_
  · rw [List.nodup_append]
    refine ⟨hown.1, ?_, ?_⟩
    · unfold List.Nodup
      rw [List.pairwise_flatMap]
      refine ⟨fun i hi => ?_, pairwise_range_of_ne fun i j hi hj hne x hx y hy => ?_⟩
      · have hi := List.mem_range.1 hi
        rcases hf i hi with e | e
        · rw [e]; exact List.nodup_nil
        · rw [e]; exact pgIds_nodup _
      · have hxi := xHas_treeHas (hmem i hi x hx)
        have hyj := xHas_treeHas (hmem j hj y hy)
        rintro rfl
        exact hu1.1 i j hi hj hne x hxi hyj
    · intro a ha b hb
      rw [hown.2 a ha]
      obtain ⟨i, hi, hbi⟩ := List.mem_flatMap.1 hb
      have hi := List.mem_range.1 hi
      have := xHas_treeHas (hmem i hi b hbi)
      rintro rfl
      exact hu1.2 i hi this
  · intro x hx
    rw [mem_xPages]
    rcases List.mem_append.1 hx with hx | hx
    · rw [hown.2 x hx]; exact xHas.root p pg hpg
    · obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.1 hx
      have hi := List.mem_range.1 hi
      exact xHas.child p pg i x hpg hfl hi (hmem i hi x hxi)

end view

end bbolt
end EtcdGrove
end Perennial
