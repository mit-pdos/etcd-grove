/-
The spill's pure tree facts (U9j, `notes/bbolt-proof-plan.md`): **a strict subtree's leaves depend
only on its pages** (`leavesF_sTree_agree`): `treeLeaves`' walk, by fuel, of an `sTree` gives the
same leaves in any page map agreeing on its pages, with any fuel above the number of its pages
(the walk descends into a child, whose tree is a strict part of its parent's, `uniqAt`). What
`UTreeFrame.treeEls_agree` needs.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.STree
public import Proof.go_etcd_io.bbolt.Model.TreeData

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace Spill

section fuel
variable [GooseExts]

/-- A page of a tree is a page of the map. -/
theorem treeHas_isSome {P : Pages} {r x : Nat} (h : treeHas P r x) : (P !! x).isSome := by
  exact treeHas.rec (pages := P)
    (motive_1 := fun _ x _ => (P !! x).isSome)
    (motive_2 := fun _ x _ => (P !! x).isSome)
    (motive_3 := fun _ x _ => (P !! x).isSome)
    (fun _ pg hpg => by simp [hpg])
    (fun _ _ _ _ _ ih => ih)
    (fun _ _ _ _ _ _ ih => ih)
    (fun _ _ _ _ _ _ _ ih => ih)
    (fun _ _ _ _ ih => ih)
    (fun _ _ _ _ ih => ih)
    h

/-- Distinct ids with pages in `P` are at most its size. -/
theorem length_le_size {P : Pages} {S : List Nat} (hnd : S.Nodup)
    (hS : ∀ x ∈ S, (P !! x).isSome) : S.length ≤ P.size := by
  have hsub : S ⊆ P.toList.map Prod.fst := by
    intro x hx
    obtain ⟨pg, hpg⟩ := Option.isSome_iff_exists.1 (hS x hx)
    exact List.mem_map.2 ⟨(x, pg), (GMap.mem_toList _ _ _).2 hpg, rfl⟩
  have := hnd.length_le_of_subset hsub
  unfold GMap.size
  simpa using this

theorem filter_len_le {α : Type} (L : List α) (p q : α → Bool)
    (hpq : ∀ x ∈ L, p x = true → q x = true) : (L.filter p).length ≤ (L.filter q).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ih' := ih (fun y hy => hpq y (List.mem_cons_of_mem _ hy))
    have ha := hpq a List.mem_cons_self
    simp only [List.filter_cons]
    cases hpa : p a <;> cases hqa : q a <;> simp_all <;> omega

theorem filter_len_lt {α : Type} (L : List α) (p q : α → Bool)
    (hpq : ∀ x ∈ L, p x = true → q x = true)
    (x : α) (hx : x ∈ L) (hq : q x = true) (hp : p x = false) :
    (L.filter p).length < (L.filter q).length := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    have hpq' : ∀ y ∈ L, p y = true → q y = true := fun y hy => hpq y (List.mem_cons_of_mem _ hy)
    have hle := filter_len_le L p q hpq'
    have ha := hpq a List.mem_cons_self
    simp only [List.filter_cons]
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp only [hp, hq]; simp; omega
    · have := ih hpq' hx'
      cases hpa : p a <;> cases hqa : q a <;> simp_all <;> omega

open Classical in
/-- The pages of `S` in the tree from `x`. -/
def muS (P : Pages) (S : List Nat) (x : Nat) : Nat :=
  (S.filter fun d => decide (treeHas P x d)).length

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- **The walk of an `sTree`'s subtree** in a map agreeing on its pages, with any fuel above its
pages in the subtree. -/
theorem leavesF_agree {P P' : Pages} {hwm id : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} (hs : sTree P hwm id lo hi h S) (hag : ∀ x ∈ S, P' !! x = P !! x) :
    ∀ n m x, treeHas P id x → treeWF P hwm x → muS P S x < n → muS P S x < m →
      leavesF n P' x = leavesF m P x
  | 0, _, _, _, _, h1, _ => absurd h1 (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _, _, h2 => absurd h2 (Nat.not_lt_zero _)
  | n + 1, m + 1, x, ht, hw, h1, h2 => by
    have hxS := (hs.has x).1 ht
    cases hw with
    | page _ pg _ _ hpg _ _ hpt =>
    simp only [leavesF]
    rw [hag x hxS, hpg]
    simp only
    by_cases hl : pageFlags pg = leafPageFlag
    · simp [hl]
    · simp only [hl, ite_false]
      apply flatMap_congr_mem
      intro i hi
      have hi' := List.mem_range.1 hi
      cases hpt with
      | leaf _ _ hfl => exact absurd hfl hl
      | branch _ _ hfl _ hch =>
        have hwy := hch i hi'
        have hpy : (P !! branchPgid pg i).isSome := by
          cases hwy with | page _ pgy _ _ hpgy => simp [hpgy]
        obtain ⟨pgy, hpgy⟩ := Option.isSome_iff_exists.1 hpy
        have hxy : treeHas P x (branchPgid pg i) :=
          treeHas.sub x pg _ hpg (pageHas.child pg i _ hfl hi' (treeHas.root _ pgy hpgy))
        have hty : treeHas P id (branchPgid pg i) := treeHas_trans ht hxy
        have hlt : muS P S (branchPgid pg i) < muS P S x := by
          classical
          unfold muS
          refine filter_len_lt S _ _ ?_ x hxS ?_ ?_
          · intro d _ hd
            simp only [decide_eq_true_eq] at hd ⊢
            exact treeHas.sub x pg d hpg (pageHas.child pg i d hfl hi' hd)
          · simp only [decide_eq_true_eq]; exact treeHas.root x pg hpg
          · simp only [decide_eq_false_iff_not]
            exact ((hs.uniq x hxS pg hpg).1 hfl).2 i hi'
        exact leavesF_agree hs hag n m _ hty hwy (by omega) (by omega)

/-- **A strict subtree's leaves depend only on its pages** (see the module doc). -/
theorem treeLeaves_sTree_agree {P P' : Pages} {hwm id : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} (hs : sTree P hwm id lo hi h S) (hag : ∀ x ∈ S, P' !! x = P !! x) :
    treeLeaves P' id = treeLeaves P id := by
  unfold treeLeaves
  have hroot : treeHas P id id := by
    cases hs.wf with | page _ pg _ _ hpg => exact treeHas.root id pg hpg
  have hmu : muS P S id ≤ S.length := by
    unfold muS; exact List.length_filter_le _ _
  have hSP : ∀ x ∈ S, (P !! x).isSome := fun x hx => treeHas_isSome ((hs.has x).2 hx)
  have h1 := length_le_size hs.nodup hSP
  have h2 := length_le_size (P := P') hs.nodup (fun x hx => by rw [hag x hx]; exact hSP x hx)
  exact leavesF_agree hs hag _ _ id hroot hs.wf (by omega) (by omega)

end fuel

end Spill

end bbolt
end EtcdGrove
end Perennial
