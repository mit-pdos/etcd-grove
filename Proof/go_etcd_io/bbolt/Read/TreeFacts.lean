/-
The read path's (U6, `notes/bbolt-proof-plan.md`) pure facts about a view's pages: every page of
a well-formed view is a well-formed tree page (its header's id, its length, a branch or a leaf).
-/
module

public import Proof.go_etcd_io.bbolt.Model.Mvcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Read

section facts
variable [GooseExts]

/-- Every page a well-formed tree reaches roots a well-formed tree. -/
theorem treeHas_treeWF (P : Pages) (hwm : Nat) {root id : Nat} (h : treeHas P root id) :
    treeWF P hwm root → treeWF P hwm id :=
  treeHas.rec (pages := P)
    (motive_1 := fun root id _ => treeWF P hwm root → treeWF P hwm id)
    (motive_2 := fun pg id _ => ∀ len, pageTreeWF P hwm pg len → treeWF P hwm id)
    (motive_3 := fun v id _ => bucketWF P hwm v → treeWF P hwm id)
    (fun _ _ _ hw => hw)
    (fun root pg id hpg _ ih hw => by
      cases hw with
      | page _ pg' _ _ hpg' _ _ hpt =>
        rw [hpg] at hpg'; cases hpg'; exact ih _ hpt)
    (fun pg i id hfl hi _ ih len hpt => by
      cases hpt with
      | leaf _ _ hfl' _ _ => rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl'
      | branch _ _ _ _ hch => exact ih (hch i hi))
    (fun pg i id hfl hi hbf _ ih len hpt => by
      cases hpt with
      | leaf _ _ _ _ hb => exact ih (hb i hi hbf)
      | branch _ _ hfl' _ _ => rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl')
    (fun v id hr _ ih hb => by
      cases hb with
      | file _ _ _ ht => exact ih ht
      | inline _ _ hr' _ _ => exact absurd hr' hr)
    (fun v id hr _ ih hb => by
      cases hb with
      | file _ _ hr' _ => exact absurd hr hr'
      | inline _ _ _ _ hpt => exact ih _ hpt)
    h

/-- The facts of a tree's root page. -/
theorem treeWF_page (P : Pages) (hwm root : Nat) (h : treeWF P hwm root) (pg : List w8)
    (hpg : P !! root = some pg) :
    2 ≤ root ∧ root < hwm ∧ pageId pg = root ∧ pg.length = (1 + pageOverflow pg) * 4096 ∧
      (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) := by
  cases h with
  | page _ pg' h2 hlt hpg' hid hlen hpt =>
    rw [hpg] at hpg'; cases hpg'
    refine ⟨h2, hlt, hid, hlen, ?_⟩
    cases hpt with
    | leaf _ _ hf _ _ => exact Or.inr hf
    | branch _ _ hf _ _ => exact Or.inl hf

/-- **A page of a well-formed view** is a tree page: its id, at least a page long, a branch or a
leaf. -/
theorem viewWF_page (v : View) (hv : viewWF v) (id : Nat) (pg : List w8)
    (hpg : v.pages !! id = some pg) :
    2 ≤ id ∧ pageId pg = id ∧ 4096 ≤ pg.length ∧
      (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  rw [hpv] at hpg
  have hfil := hok.2.1
  have hin : treePages C.pages C.root !! id = some pg := by rw [hfil]; exact hpg
  unfold treePages at hin
  rw [GMap.mapLookup_filter_Some] at hin
  have hhas : treeHas C.pages C.root id := by simpa using hin.2
  have hw := treeHas_treeWF C.pages C.hwm hhas hok.1.1
  obtain ⟨h2, _, hid, hlen, hf⟩ := treeWF_page _ _ _ hw pg hpg
  exact ⟨h2, hid, by rw [hlen]; omega, hf⟩

end facts

end Read

end bbolt
end EtcdGrove
end Perennial
