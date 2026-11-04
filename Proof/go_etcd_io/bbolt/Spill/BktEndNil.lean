/-
`Bucket.spill`'s root loop's end (U9x5, `notes/bbolt-proof-plan.md`), part 3: **the root bucket's
base tree when it has no root node** (`end_nilTree'`, for `BktEnd.rinv_end_nil`): its tree at its header's
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


/-- **Every base slot is the base tree's or pending** (no root node, every cached child without
one): `spillPre`'s coverage; a covering position is the root's (a page under its root page), a
cached child's (under its value's root, an entry of a root page), or no other bucket's
(`derefPre`, `liveReach`: every bucket the root or a cached child, whose cache is empty); an
unopened bucket's value is an entry of a root page. -/
theorem nil_cover {X : WX} {fl : FLPg} {C : CommitSt} {B0 : BRec} (hpre : spillPre X fl)
    (hreach : liveReach X) (hfv : flViewU X fl) (hB0 : X.t.bs !! X.rl = some B0)
    (hrn : B0.bv.rootNode' = null)
    (hkids : ∀ k c, B0.bm !! k = some c → ∃ C0, X.t.bs !! c = some C0 ∧ C0.bv.rootNode' = null)
    (hcp : X.v.pages = C.pages) (hcok : treeOK C) :
    ∀ s ∈ treeSlots C, s ∈ pgSlots (spP X) (subPages C.pages X.rootPage) ∨ s ∈ pendSlots fl := by
  sorry

/-- **The base tree's elements give the root shape and the writer's data** (`endEls`; the root's
leaf pages' entries bucket entries within the bounds, `posShape`; their nested buckets' leaves
plain, the committed tree's `rootShape` below the root page; the names `rootEnts` (the logical
tree reads the pages, `lleaves_pages`); a cached child's entries its value's tree's). -/
theorem nil_els {X : WX} {fl : FLPg} {C : CommitSt} {B0 : BRec} (hpre : spillPre X fl)
    (hreach : liveReach X) (hB0 : X.t.bs !! X.rl = some B0) (hrn : B0.bv.rootNode' = null)
    (hkids : ∀ k c, B0.bm !! k = some c → ∃ C0, X.t.bs !! c = some C0 ∧ C0.bv.rootNode' = null)
    (hcp : X.v.pages = C.pages) (hcok : treeOK C) :
    endEls X (spP X) (pgSlots (spP X) (subPages C.pages X.rootPage))
      (treeEls (spP X) X.rootPage) := by
  sorry

/-- **The root bucket's base tree at the end with no root node** (`end_nilTree`'s statement). -/
theorem end_nilTree' {X0 : WX} {w0 : WDb} {B0 : BRec}
    (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hrn : B0.bv.rootNode' = null)
    (hkids : ∀ k c, B0.bm !! k = some c →
      ∃ C0, X0.t.bs !! c = some C0 ∧ C0.bv.rootNode' = null)
    (hvC : X0.v = View.ofC X0.v.base w0.C) (hcok : treeOK w0.C)
    (hhwm : w0.C.hwm ≤ X0.t.mv.pgid'.toNat) :
    ∃ h S, sTree (spP X0) X0.t.mv.pgid'.toNat X0.rootPage none none h S ∧
      (∀ s ∈ treeSlots w0.C, s ∈ pgSlots (spP X0) S ∨ s ∈ pendSlots w0.fl) ∧
      (∀ s ∈ pgSlots (spP X0) S, s ∈ treeSlots w0.C) ∧
      endEls X0 (spP X0) (pgSlots (spP X0) S) (treeEls (spP X0) X0.rootPage) := by
  have hcp : X0.v.pages = w0.C.pages := by
    have := congrArg View.pages hvC; simpa [View.ofC] using this
  obtain ⟨h, hs⟩ := nil_sTree hpre hB0 hrn hcp hcok hhwm
  have hP : spP X0 = w0.C.pages := by rw [spP_clean hpre.1.1.2.1.2.1, hcp]
  exact ⟨h, _, hs, nil_cover hpre hreach hfv hB0 hrn hkids hcp hcok, nil_slots hP _,
    nil_els hpre hreach hB0 hrn hkids hcp hcok⟩

end nil

end Spill

end bbolt
end EtcdGrove
end Perennial
