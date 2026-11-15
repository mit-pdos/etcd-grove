/-
The view's nested-plainness bound (`matNest`): a leaf page's bucket entries' own leaves hold plain
entries with non-empty keys within `bboltEntryMax` (`bvalOK`'s third clause), for every page of a
well-formed view (`viewWF_matNest`, from `treeOK`'s `rootShape` over `treeHas`, as
`Write/Bound.viewWF_leafInl`). Pure.
-/
module

public import Proof.go_etcd_io.bbolt.Write.Bound

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section nest
variable [GooseExts]

/-- A leaf page's bucket entries' own leaves are plain, their keys non-empty and entries bounded
(`bvalOK`'s third clause for every bucket entry of the page): every view page's
(`viewWF_matNest`). -/
def matNest (P : Pages) (pg : List w8) : Prop :=
  pageFlags pg = leafPageFlag → ∀ j < pageCount pg, leafFlags pg j % 2 = bucketLeafFlag →
    ∀ bpg, bktLeafPg P (leafValue pg j) bpg → ∀ k < pageCount bpg,
      leafFlags bpg k % 2 = 0 ∧ 0 < leafKsize bpg k ∧ leafKsize bpg k + leafVsize bpg k ≤ bboltEntryMax

/-- Every page a top-level or nested tree reaches has `matNest` (a root-shaped tree's leaves:
`rootShape`'s nested clause; a nested tree has no bucket entry). -/
theorem treeHas_matNest (P : Pages) (hwm : Nat) {root id : Nat} (h : treeHas P root id) :
    treeWF P hwm root → (rootShape P root ∨ Write.nestBnd P root) →
      ∀ pg, P !! id = some pg → matNest P pg :=
  treeHas.rec (pages := P)
    (motive_1 := fun root id _ => treeWF P hwm root → (rootShape P root ∨ Write.nestBnd P root) →
      ∀ pg, P !! id = some pg → matNest P pg)
    (motive_2 := fun pg id _ => ∀ len, pageTreeWF P hwm pg len →
      (Write.topPg P pg ∨ Write.nestPg P pg) → ∀ pg', P !! id = some pg' → matNest P pg')
    (motive_3 := fun v id _ => bucketWF P hwm v → Write.bvBnd P v →
      ∀ pg', P !! id = some pg' → matNest P pg')
    (fun root pg hpg _ hs pg' hpg' => by
      rw [hpg] at hpg'; cases hpg'
      intro hl i hi hb bpg hbp j hj
      rcases hs with hs | hs
      · exact (hs root pg (ownHas.root _ pg hpg) hpg hl i hi).2.2.2 bpg hbp j hj
      · have := (hs root pg (ownHas.root _ pg hpg) hpg hl i hi).1
        rw [hb] at this; unfold bucketLeafFlag at this; omega)
    (fun root pg id hpg _ ih hw hs => by
      cases hw with
      | page _ pg' _ _ hpg' _ _ hpt =>
        rw [hpg] at hpg'; cases hpg'
        refine ih _ hpt ?_
        rcases hs with hs | hs
        · exact Or.inl (Write.topPg_of P root pg hs hpg)
        · exact Or.inr (Write.nestPg_of P root pg hs hpg))
    (fun pg i id hfl hi _ ih len hpt hs => by
      cases hpt with
      | leaf _ _ hfl' _ _ => rw [hfl] at hfl'; exact absurd hfl'.symm Write.leaf_ne_branch
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
      | branch _ _ hfl' _ _ => rw [hfl] at hfl'; exact absurd hfl' Write.leaf_ne_branch)
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
        rw [hfl] at hb; exact absurd hb Write.leaf_ne_branch)
    h

/-- **Every page of a well-formed view has `matNest`** (as `Write.viewWF_leafInl`). -/
theorem viewWF_matNest (v : View) (hv : viewWF v) (id : Nat) (pg : List w8)
    (hpg : v.pages !! id = some pg) : matNest v.pages pg := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  rw [hpv] at hpg ⊢
  have hin : treePages C.pages C.root !! id = some pg := by rw [hok.2.1]; exact hpg
  unfold treePages at hin
  rw [GMap.mapLookup_filter_Some] at hin
  have hhas : treeHas C.pages C.root id := by simpa using hin.2
  exact treeHas_matNest C.pages C.hwm hhas hok.1.1 (Or.inl hok.2.2.2.2.1) pg hpg

end nest

end bbolt
end EtcdGrove
end Perennial
