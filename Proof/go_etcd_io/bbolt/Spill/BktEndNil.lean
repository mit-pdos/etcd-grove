/-
`Bucket.spill`'s root loop's end (U9x5, `notes/bbolt-proof-plan.md`), part 3: **the root bucket's
base tree when it has no root node** (pieces of `BktEndTree.end_nilTree`): its tree at its header's
root page is a subtree of the committed tree (`sTree_base`), over the spill's page map (no buffer
yet), its slots base slots.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktEndTree
public import Proof.go_etcd_io.bbolt.Spill.BktSlot

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section nil
variable [GooseExts]

theorem rootPage_of {X : WX} {B : BRec} (hB : X.t.bs !! X.rl = some B) :
    X.rootPage = B.ib.root'.toNat := by
  unfold WX.rootPage; rw [hB]; rfl

/-- A page of the view lies in the committed tree. -/
theorem treeHas_of_page {C : CommitSt} (hcok : treeOK C) {x : Nat} {pg : List w8}
    (hpg : C.pages !! x = some pg) : treeHas C.pages C.root x := by
  have e : treePages C.pages C.root !! x = some pg := by rw [hcok.2.1]; exact hpg
  rw [treePages_lookup] at e
  split at e
  · assumption
  · cases e

/-- **The root bucket's base tree** (no root node, no buffer): an `sTree` over the spill's page
map at its header's root page, its pages the committed tree's below it. -/
theorem nil_sTree {X : WX} {fl : FLPg} {C : CommitSt} {B0 : BRec} (hpre : spillPre X fl)
    (hB0 : X.t.bs !! X.rl = some B0) (hrn : B0.bv.rootNode' = null)
    (hcp : X.v.pages = C.pages) (hcok : treeOK C) (hhwm : C.hwm ≤ X.t.mv.pgid'.toNat) :
    ∃ h, sTree (spP X) X.t.mv.pgid'.toNat X.rootPage none none h
      (subPages C.pages X.rootPage) := by
  have hok := hpre.1
  have htc := hok.1
  have hP : spP X = X.v.pages := spP_clean htc.2.1.2.1
  have h0 : B0.ib.root' ≠ W64 0 := htc.2.1.2.2.2.2 B0 hB0
  have hcl := (htc.2.2.2.2.2 X.rl B0 hB0).1
  have hwf : treeWF X.v.pages X.t.mv.pgid'.toNat B0.ib.root'.toNat := (hcl.2.1 h0).2 hrn
  obtain ⟨bnd, hbk⟩ := (hok.2.1 X.rl B0 hB0).1
  have hk : treeKeys X.v.pages B0.ib.root'.toNat none none := hbk.1 hrn h0
  rw [rootPage_of hB0, hP]
  obtain ⟨pg, hpg⟩ := treeWF_page_some hwf
  rw [hcp] at hpg hk
  have ht := treeHas_of_page hcok hpg
  obtain ⟨pht, hpht⟩ := hcok.1.2.2.2
  have hs := sTree_base C hcok ht hk pht hpht
  exact ⟨pht _, sTree_agree (fun x _ => by rw [hcp]) hhwm hs⟩

/-- **The base tree's slots are base slots.** -/
theorem nil_slots {X : WX} {C : CommitSt} (hP : spP X = C.pages) (root : Nat) :
    ∀ s ∈ pgSlots (spP X) (subPages C.pages root), s ∈ treeSlots C := by
  intro s hs
  rw [hP] at hs
  unfold pgSlots at hs
  obtain ⟨x, hx, hsx⟩ := List.mem_flatMap.1 hs
  obtain ⟨pg, hpg⟩ := treeHas_page (mem_subPages.1 hx)
  rw [hpg] at hsx
  simp only [List.mem_range'] at hsx
  obtain ⟨i, hi, rfl⟩ := hsx
  exact mem_pagesSlots.2 ⟨x, pg, hpg, by omega, by omega⟩

end nil

end Spill

end bbolt
end EtcdGrove
end Perennial
