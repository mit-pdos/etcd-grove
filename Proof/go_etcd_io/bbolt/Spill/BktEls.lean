/-
`Bucket.spill`'s initial trees (U9i, `notes/bbolt-proof-plan.md`), part 2: **the leaf elements of
a page subtree of the logical tree**. Where the logical tree reads a well-formed subtree's pages
(`ltree` at a page position, no node of its subtree materialized), its leaves are the pages'
(`lleaves_pages`), and its entries by data the pages' leaf elements (`treeEls`), so the leaf
elements of an unspilled tree's finished subtree (`fTree`) are its logical entries.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTree
public import Proof.go_etcd_io.bbolt.Model.LTree

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section els
variable [GooseExts]

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem branchPgid_toNat' (pg : List w8) (i : Nat) :
    (W64 (branchPgid pg i : Int)).toNat = branchPgid pg i := by
  unfold branchPgid; simp

/-- What the logical tree reads at a page position: the page's kind and entries. -/
def pgRead (pg : List w8) : Bool × List WEntry := (decide (pageFlags pg = leafPageFlag), pageWs pg)

/-- **The logical tree's leaves over a page subtree** are the pages' (read as entries). -/
theorem lleaves_pages (L : LTree) (bl : Loc) (P : Pages) (hwm : Nat) :
    ∀ n (pid : w64), treeWF P hwm pid.toNat →
      (∀ q : w64, treeHas P pid.toNat q.toNat → L bl q = (P !! q.toNat).map pgRead) →
      lleaves L bl n pid = (leavesF n P pid.toNat).map pageWs
  | 0, _, _, _ => rfl
  | n + 1, pid, hw, hL => by
    cases hw with
    | page _ pg _ _ hpg _ _ hpt =>
    simp only [lleaves, leavesF]
    rw [hL pid (treeHas.root _ pg hpg), hpg]
    simp only [Option.map_some, pgRead]
    by_cases hl : pageFlags pg = leafPageFlag
    · simp [hl]
    · simp only [hl, decide_false, ite_false]
      rw [List.map_flatMap]
      unfold pageWs
      rw [List.flatMap_map]
      apply flatMap_congr'
      intro i hi
      have hi' := List.mem_range.1 hi
      have hpw : (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by simp [pageW, hl]
      cases hpt with
      | leaf _ _ hfl => exact absurd hfl hl
      | branch _ _ hfl _ hch =>
        rw [hpw]
        have hw' := hch i hi'
        rw [← branchPgid_toNat' pg i] at hw'
        have hL' : ∀ q : w64, treeHas P (W64 (branchPgid pg i : Int)).toNat q.toNat →
            L bl q = (P !! q.toNat).map pgRead := by
          intro q hq
          rw [branchPgid_toNat'] at hq
          exact hL q (treeHas.sub _ pg _ hpg (pageHas.child pg i _ hfl hi' hq))
        rw [lleaves_pages L bl P hwm n _ hw' hL', branchPgid_toNat']
        rfl

/-- The pages a walk reaches are leaves. -/
theorem leavesF_leaf' (P : Pages) : ∀ n id pg, pg ∈ leavesF n P id → pageFlags pg = leafPageFlag
  | 0, _, _, h => by simp [leavesF] at h
  | n + 1, id, pg, h => by
    simp only [leavesF] at h
    cases hp : P !! id with
    | none => rw [hp] at h; simp at h
    | some pg' =>
      rw [hp] at h
      simp only at h
      by_cases hl : pageFlags pg' = leafPageFlag
      · rw [if_pos hl, List.mem_singleton] at h; subst h; exact hl
      · rw [if_neg hl, List.mem_flatMap] at h
        obtain ⟨i, -, hm⟩ := h
        exact leavesF_leaf' P n _ pg hm

theorem leafFlags_lt (pg : List w8) (i : Nat) : leafFlags pg i < 2 ^ 32 := by
  unfold leafFlags; exact BitVec.isLt _

/-- A leaf page's entries by data are its leaf elements. -/
theorem pageWs_els (pg : List w8) (hl : pageFlags pg = leafPageFlag) :
    (pageWs pg).map wEl =
      (List.range (pageCount pg)).map fun i => (leafFlags pg i, leafKey pg i, leafValue pg i) := by
  unfold pageWs
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, wEl, pageW, if_pos hl]
  have := leafFlags_lt pg i
  congr 1
  simp only [BitVec.toNat_ofInt]
  omega

/-- **The leaf elements of a walk's leaves**, read as entries. -/
theorem leavesF_els (P : Pages) (n id : Nat) :
    ((leavesF n P id).map pageWs).flatMap (List.map wEl) =
      (leavesF n P id).flatMap fun pg =>
        (List.range (pageCount pg)).map fun i => (leafFlags pg i, leafKey pg i, leafValue pg i) := by
  rw [List.flatMap_map]
  apply flatMap_congr'
  intro pg hpg
  exact pageWs_els pg (leavesF_leaf' P n id pg hpg)

end els

end Spill

end bbolt
end EtcdGrove
end Perennial
