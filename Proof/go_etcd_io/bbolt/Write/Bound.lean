/-
The view's bounds on a leaf page's entries (moved from `Write/MatOK`, batch 30, unchanged, so
that `Rebalance/RblMat` can use them): `leafBnd` (plain entries within `bboltEntryMax`,
`viewWF_leafBnd`) and `leafInl` (inline nested buckets' pages within the bound, `inlineBnd`,
`viewWF_leafInl`), from `treeOK`'s `rootShape` over `treeHas`. Pure; `Write/MatOK` re-exports it.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Wtx
public import Proof.go_etcd_io.bbolt.Model.Mvcc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section bound
variable [GooseExts]

/-- A leaf page's plain entries are within `bboltEntryMax`. -/
def leafBnd (pg : List w8) : Prop :=
  pageFlags pg = leafPageFlag → ∀ i < pageCount pg, leafFlags pg i % 2 = 0 →
    leafKsize pg i + leafVsize pg i ≤ bboltEntryMax

/-- A bucket value whose leaves hold plain entries within the bound. -/
def bvBnd (P : Pages) (v : List w8) : Prop :=
  ∀ bpg, bktLeafPg P v bpg → ∀ j < pageCount bpg,
    leafFlags bpg j % 2 = 0 ∧ leafKsize bpg j + leafVsize bpg j ≤ bboltEntryMax

/-- A nested bucket's tree: its leaves hold plain entries within the bound. -/
def nestBnd (P : Pages) (r : Nat) : Prop :=
  ∀ id pg, ownHas P r id → P !! id = some pg → pageFlags pg = leafPageFlag →
    ∀ j < pageCount pg, leafFlags pg j % 2 = 0 ∧ leafKsize pg j + leafVsize pg j ≤ bboltEntryMax

def topPg (P : Pages) (pg : List w8) : Prop :=
  (pageFlags pg = leafPageFlag → ∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag ∧
    bvBnd P (leafValue pg i)) ∧
  (pageFlags pg = branchPageFlag → ∀ i < pageCount pg, rootShape P (branchPgid pg i))

def nestPg (P : Pages) (pg : List w8) : Prop :=
  (pageFlags pg = leafPageFlag → ∀ j < pageCount pg,
    leafFlags pg j % 2 = 0 ∧ leafKsize pg j + leafVsize pg j ≤ bboltEntryMax) ∧
  (pageFlags pg = branchPageFlag → ∀ i < pageCount pg, nestBnd P (branchPgid pg i))

theorem topPg_of (P : Pages) (r : Nat) (pg : List w8) (hs : rootShape P r)
    (hpg : P !! r = some pg) : topPg P pg := by
  refine ⟨fun hl i hi => ?_, fun hb i hi => ?_⟩
  · obtain ⟨h1, -, -, h3⟩ := hs r pg (ownHas.root _ pg hpg) hpg hl i hi
    exact ⟨h1, fun bpg hb j hj => ⟨(h3 bpg hb j hj).1, (h3 bpg hb j hj).2.2⟩⟩
  · intro id pg' ho hp hl'
    exact hs id pg' (ownHas.child _ pg i id hpg hb hi ho) hp hl'

theorem nestPg_of (P : Pages) (r : Nat) (pg : List w8) (hs : nestBnd P r)
    (hpg : P !! r = some pg) : nestPg P pg := by
  refine ⟨fun hl j hj => hs r pg (ownHas.root _ pg hpg) hpg hl j hj, fun hb i hi => ?_⟩
  intro id pg' ho hp hl'
  exact hs id pg' (ownHas.child _ pg i id hpg hb hi ho) hp hl'

theorem leaf_ne_branch : leafPageFlag ≠ branchPageFlag := by
  unfold branchPageFlag leafPageFlag; decide

/-- Every page a top-level or nested tree reaches has its plain entries within the bound. -/
theorem treeHas_leafBnd (P : Pages) (hwm : Nat) {root id : Nat} (h : treeHas P root id) :
    treeWF P hwm root → (rootShape P root ∨ nestBnd P root) →
      ∀ pg, P !! id = some pg → leafBnd pg :=
  treeHas.rec (pages := P)
    (motive_1 := fun root id _ => treeWF P hwm root → (rootShape P root ∨ nestBnd P root) →
      ∀ pg, P !! id = some pg → leafBnd pg)
    (motive_2 := fun pg id _ => ∀ len, pageTreeWF P hwm pg len → (topPg P pg ∨ nestPg P pg) →
      ∀ pg', P !! id = some pg' → leafBnd pg')
    (motive_3 := fun v id _ => bucketWF P hwm v → bvBnd P v →
      ∀ pg', P !! id = some pg' → leafBnd pg')
    (fun root pg hpg _ hs pg' hpg' => by
      rw [hpg] at hpg'; cases hpg'
      intro hl i hi h0
      rcases hs with hs | hs
      · have := (hs root pg (ownHas.root _ pg hpg) hpg hl i hi).1
        unfold bucketLeafFlag at this; omega
      · exact (hs root pg (ownHas.root _ pg hpg) hpg hl i hi).2)
    (fun root pg id hpg _ ih hw hs => by
      cases hw with
      | page _ pg' _ _ hpg' _ _ hpt =>
        rw [hpg] at hpg'; cases hpg'
        refine ih _ hpt ?_
        rcases hs with hs | hs
        · exact Or.inl (topPg_of P root pg hs hpg)
        · exact Or.inr (nestPg_of P root pg hs hpg))
    (fun pg i id hfl hi _ ih len hpt hs => by
      cases hpt with
      | leaf _ _ hfl' _ _ => rw [hfl] at hfl'; exact absurd hfl'.symm leaf_ne_branch
      | branch _ _ _ _ hch =>
        refine ih (hch i hi) ?_
        rcases hs with hs | hs
        · exact Or.inl (hs.2 hfl i hi)
        · exact Or.inr (hs.2 hfl i hi))
    (fun pg i id hfl hi hbf _ ih len hpt hs => by
      cases hpt with
      | leaf _ _ _ _ hb =>
        refine ih (hb i hi hbf) ?_
        rcases hs with hs | hs
        · exact (hs.1 hfl i hi).2
        · have := (hs.1 hfl i hi).1; rw [hbf] at this; unfold bucketLeafFlag at this; omega
      | branch _ _ hfl' _ _ => rw [hfl] at hfl'; exact absurd hfl' leaf_ne_branch)
    (fun v id hr _ ih hb hbv => by
      cases hb with
      | file _ _ _ ht =>
        refine ih ht (Or.inr ?_)
        intro id' pg ho hp hl j hj
        exact hbv pg (Or.inr ⟨hr, id', ho, hp, hl⟩) j hj
      | inline _ _ hr' _ _ => exact absurd hr' hr)
    (fun v id hr _ ih hb hbv => by
      cases hb with
      | file _ _ hr' _ => exact absurd hr hr'
      | inline _ _ _ hfl hpt =>
        refine ih _ hpt (Or.inr ⟨fun _ j hj => hbv _ (Or.inl ⟨hr, rfl⟩) j hj, fun hb => ?_⟩)
        rw [hfl] at hb; exact absurd hb leaf_ne_branch)
    h

/-- A leaf page's inline nested buckets' pages are within the bound (`inlineBnd`, batch 22). -/
def leafInl (pg : List w8) : Prop :=
  pageFlags pg = leafPageFlag → ∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag →
    inBucketRoot (leafValue pg i) = 0 → inlineBnd (inlinePage (leafValue pg i))

theorem treeHas_leafInl (P : Pages) (hwm : Nat) {root id : Nat} (h : treeHas P root id) :
    treeWF P hwm root → (rootShape P root ∨ nestBnd P root) →
      ∀ pg, P !! id = some pg → leafInl pg :=
  treeHas.rec (pages := P)
    (motive_1 := fun root id _ => treeWF P hwm root → (rootShape P root ∨ nestBnd P root) →
      ∀ pg, P !! id = some pg → leafInl pg)
    (motive_2 := fun pg id _ => ∀ len, pageTreeWF P hwm pg len → (topPg P pg ∨ nestPg P pg) →
      ∀ pg', P !! id = some pg' → leafInl pg')
    (motive_3 := fun v id _ => bucketWF P hwm v → bvBnd P v →
      ∀ pg', P !! id = some pg' → leafInl pg')
    (fun root pg hpg _ hs pg' hpg' => by
      rw [hpg] at hpg'; cases hpg'
      intro hl i hi hb h0 j hj
      rcases hs with hs | hs
      · exact ((hs root pg (ownHas.root _ pg hpg) hpg hl i hi).2.2.2 _ (Or.inl ⟨h0, rfl⟩) j hj).2.2
      · have := (hs root pg (ownHas.root _ pg hpg) hpg hl i hi).1
        rw [hb] at this; unfold bucketLeafFlag at this; omega)
    (fun root pg id hpg _ ih hw hs => by
      cases hw with
      | page _ pg' _ _ hpg' _ _ hpt =>
        rw [hpg] at hpg'; cases hpg'
        refine ih _ hpt ?_
        rcases hs with hs | hs
        · exact Or.inl (topPg_of P root pg hs hpg)
        · exact Or.inr (nestPg_of P root pg hs hpg))
    (fun pg i id hfl hi _ ih len hpt hs => by
      cases hpt with
      | leaf _ _ hfl' _ _ => rw [hfl] at hfl'; exact absurd hfl'.symm leaf_ne_branch
      | branch _ _ _ _ hch =>
        refine ih (hch i hi) ?_
        rcases hs with hs | hs
        · exact Or.inl (hs.2 hfl i hi)
        · exact Or.inr (hs.2 hfl i hi))
    (fun pg i id hfl hi hbf _ ih len hpt hs => by
      cases hpt with
      | leaf _ _ _ _ hb =>
        refine ih (hb i hi hbf) ?_
        rcases hs with hs | hs
        · exact (hs.1 hfl i hi).2
        · have := (hs.1 hfl i hi).1; rw [hbf] at this; unfold bucketLeafFlag at this; omega
      | branch _ _ hfl' _ _ => rw [hfl] at hfl'; exact absurd hfl' leaf_ne_branch)
    (fun v id hr _ ih hb hbv => by
      cases hb with
      | file _ _ _ ht =>
        refine ih ht (Or.inr ?_)
        intro id' pg ho hp hl j hj
        exact hbv pg (Or.inr ⟨hr, id', ho, hp, hl⟩) j hj
      | inline _ _ hr' _ _ => exact absurd hr' hr)
    (fun v id hr _ ih hb hbv => by
      cases hb with
      | file _ _ hr' _ => exact absurd hr hr'
      | inline _ _ _ hfl hpt =>
        refine ih _ hpt (Or.inr ⟨fun _ j hj => hbv _ (Or.inl ⟨hr, rfl⟩) j hj, fun hb => ?_⟩)
        rw [hfl] at hb; exact absurd hb leaf_ne_branch)
    h

/-- **Every leaf page of a well-formed view bounds its inline nested buckets' pages** (the root's
leaves: `rootShape`'s bucket values; below a top-level bucket there is no nested bucket). -/
theorem viewWF_leafInl (v : View) (hv : viewWF v) (id : Nat) (pg : List w8)
    (hpg : v.pages !! id = some pg) : leafInl pg := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  rw [hpv] at hpg
  have hin : treePages C.pages C.root !! id = some pg := by rw [hok.2.1]; exact hpg
  unfold treePages at hin
  rw [GMap.mapLookup_filter_Some] at hin
  have hhas : treeHas C.pages C.root id := by simpa using hin.2
  exact treeHas_leafInl C.pages C.hwm hhas hok.1.1 (Or.inl hok.2.2.2.2.1) pg hpg

/-- **Every leaf page of a well-formed view has its plain entries within `bboltEntryMax`**
(`treeOK`'s `rootShape`: the root's leaves hold buckets only, their leaves plain entries within
the bound; every page of the view is the tree's). -/
theorem viewWF_leafBnd (v : View) (hv : viewWF v) (id : Nat) (pg : List w8)
    (hpg : v.pages !! id = some pg) : leafBnd pg := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  rw [hpv] at hpg
  have hin : treePages C.pages C.root !! id = some pg := by rw [hok.2.1]; exact hpg
  unfold treePages at hin
  rw [GMap.mapLookup_filter_Some] at hin
  have hhas : treeHas C.pages C.root id := by simpa using hin.2
  exact treeHas_leafBnd C.pages C.hwm hhas hok.1.1 (Or.inl hok.2.2.2.2.1) pg hpg

end bound

end Write

end bbolt
end EtcdGrove
end Perennial
