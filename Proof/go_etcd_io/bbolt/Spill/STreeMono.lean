/-
The spill's pure tree facts (U9d, `notes/bbolt-proof-plan.md`), part 3: an `sTree` stays one in
a larger page map (the written buffers grow as the spill allocates) and below a higher mark (the
high-water mark grows).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.STree
public import Proof.go_etcd_io.bbolt.Read.TreeFacts

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Spill

section mono
variable [GooseExts]

/-- A page of a tree is a page of the map. -/
theorem treeHas_page {P : Pages} {r y : Nat} (h : treeHas P r y) : ∃ pg, P !! y = some pg :=
  treeHas.rec (pages := P)
    (motive_1 := fun _ y _ => ∃ pg, P !! y = some pg)
    (motive_2 := fun _ y _ => ∃ pg, P !! y = some pg)
    (motive_3 := fun _ y _ => ∃ pg, P !! y = some pg)
    (fun _ pg hpg => ⟨pg, hpg⟩) (fun _ _ _ _ _ ih => ih) (fun _ _ _ _ _ _ ih => ih)
    (fun _ _ _ _ _ _ _ ih => ih) (fun _ _ _ _ ih => ih) (fun _ _ _ _ ih => ih) h

/-- A page of a nested bucket's tree is a page of the map. -/
theorem bucketHas_page {P : Pages} {v : List w8} {y : Nat} (h : bucketHas P v y) :
    ∃ pg, P !! y = some pg :=
  bucketHas.rec (pages := P)
    (motive_1 := fun _ y _ => ∃ pg, P !! y = some pg)
    (motive_2 := fun _ y _ => ∃ pg, P !! y = some pg)
    (motive_3 := fun _ y _ => ∃ pg, P !! y = some pg)
    (fun _ pg hpg => ⟨pg, hpg⟩) (fun _ _ _ _ _ ih => ih) (fun _ _ _ _ _ _ ih => ih)
    (fun _ _ _ _ _ _ _ ih => ih) (fun _ _ _ _ ih => ih) (fun _ _ _ _ ih => ih) h

/-- A well-formed tree is well-formed below a higher mark. -/
theorem treeWF_hwm {P : Pages} {hwm hwm' root : Nat} (hle : hwm ≤ hwm') (h : treeWF P hwm root) :
    treeWF P hwm' root :=
  treeWF.rec (pages := P) (hwm := hwm)
    (motive_1 := fun root _ => treeWF P hwm' root)
    (motive_2 := fun pg len _ => pageTreeWF P hwm' pg len)
    (motive_3 := fun v _ => bucketWF P hwm' v)
    (fun root pg h2 hlt hpg hid hlen _ ih => treeWF.page root pg h2 (by omega) hpg hid hlen ih)
    (fun pg len hfl hlw _ ih => pageTreeWF.leaf pg len hfl hlw ih)
    (fun pg len hfl hbw _ ih => pageTreeWF.branch pg len hfl
      ⟨hbw.1, hbw.2.1, hbw.2.2.1, fun i hi => ⟨(hbw.2.2.2.1 i hi).1, (hbw.2.2.2.1 i hi).2.1,
        by have := (hbw.2.2.2.1 i hi).2.2; omega⟩, hbw.2.2.2.2⟩ ih)
    (fun v h16 hr _ ih => bucketWF.file v h16 hr ih)
    (fun v h16 hr hfl _ ih => bucketWF.inline v h16 hr hfl ih)
    h

/-- A well-formed tree's leaf page's nested buckets are well-formed. -/
theorem treeWF_leaf_bucketWF {P : Pages} {hwm r : Nat} (h : treeWF P hwm r) {pg : List w8}
    (hpg : P !! r = some pg) (hfl : pageFlags pg = leafPageFlag) {i : Nat} (hi : i < pageCount pg)
    (hbf : leafFlags pg i % 2 = bucketLeafFlag) : bucketWF P hwm (leafValue pg i) := by
  cases h with
  | page _ pg' _ _ hpg' _ _ hpt =>
    rw [hpg] at hpg'; cases hpg'
    cases hpt with
    | leaf _ _ _ _ hb => exact hb i hi hbf
    | branch _ _ hfl' _ _ => rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl'

/-- A well-formed tree's branch page's children are well-formed trees. -/
theorem treeWF_branch_child {P : Pages} {hwm r : Nat} (h : treeWF P hwm r) {pg : List w8}
    (hpg : P !! r = some pg) (hfl : pageFlags pg = branchPageFlag) {i : Nat}
    (hi : i < pageCount pg) : treeWF P hwm (branchPgid pg i) := by
  cases h with
  | page _ pg' _ _ hpg' _ _ hpt =>
    rw [hpg] at hpg'; cases hpg'
    cases hpt with
    | leaf _ _ hfl' _ _ => rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl'
    | branch _ _ _ _ hch => exact hch i hi

/-- **An `sTree` in a larger map, below a higher mark.** -/
theorem sTree_mono {P P' : Pages} {hwm hwm' id : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} (hle : pagesLe P P') (hh : hwm ≤ hwm') (hs : sTree P hwm id lo hi h S) :
    sTree P' hwm' id lo hi h S := by
  -- the tree's pages agree
  have hag : ∀ y, treeHas P id y → P' !! y = P !! y := by
    intro y hy
    obtain ⟨pg, hpg⟩ := treeHas_page hy
    rw [hpg]; exact hle _ _ hpg
  have hS : ∀ x ∈ S, ∀ pg, P' !! x = some pg → P !! x = some pg := by
    intro x hx pg hp
    rw [← hag x ((hs.has x).2 hx)]; exact hp
  have hiff : ∀ x, treeHas P' id x ↔ treeHas P id x :=
    fun x => ⟨fun h' => treeHas_of_le hle hwm h' hs.wf, treeHas_le hle⟩
  refine ⟨treeWF_hwm hh (treeWF_agree hs.wf hag), treeKeys_agree hs.keys hag,
    fun x => (hiff x).trans (hs.has x), hs.nodup, fun x hx pg hp => hs.good x hx pg (hS x hx pg hp),
    fun x hx pg hp => ?_, ?_, fun x hx y hy hne pgx pgy hpx hpy =>
      hs.disj x hx y hy hne pgx pgy (hS x hx pgx hpx) (hS y hy pgy hpy),
    fun x hx pg hp => by have := hs.ext x hx pg (hS x hx pg hp); omega⟩
  · have hp' := hS x hx pg hp
    have hxt : treeHas P id x := (hs.has x).2 hx
    have hwx : treeWF P hwm x := Read.treeHas_treeWF P hwm hxt hs.wf
    refine uniqAt_congr (fun i hi hb d => ⟨fun h' => ?_, treeHas_le hle⟩)
      (fun i hi hl hbf d => ⟨fun h' => ?_, bucketHas_le hle⟩) (hs.uniq x hx pg hp')
    · exact treeHas_of_le hle hwm h' (treeWF_branch_child hwx hp' hb hi)
    · exact bucketHas_of_le hle hwm h' (treeWF_leaf_bucketWF hwx hp' hl hi hbf)
  · obtain ⟨pht, hpht, hid⟩ := hs.hts
    exact ⟨pht, fun x hx pg hp => hpht x hx pg (hS x hx pg hp), hid⟩

end mono

end Spill

end bbolt
end EtcdGrove
end Perennial
