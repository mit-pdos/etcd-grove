/-
`Bucket.spill`'s root loop (U9x7, `notes/bbolt-proof-plan.md`): **the root bucket's extents through
its search and put** (`RInv.rootExt`): a materialization (`nodeAdded`) keeps the logical tree by
data and gives the new node the page id of its position (the page's header id, `treeWF`), so each
position keeps its page id (`extents_matGrow`); a put into a leaf keeps the shape and the leaf's
page id (`extents_setLeaf`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopExt
public import Proof.go_etcd_io.bbolt.Spill.BktLoopPurePut
public import Proof.go_etcd_io.bbolt.Spill.BktLoopPureRPutT

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section extmat
variable [GooseExts]

/-- **A put into a leaf keeps the bucket's extents.** -/
theorem extents_setLeaf {X : WX} {bl l : Loc} {B : BRec} {r r' : NRec}
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r) (hlf : r.nv.isLeaf' = true)
    (hlf' : r'.nv.isLeaf' = true) (hpg : r'.nv.pgid' = r.nv.pgid') :
    (X.setNode bl l r').extents bl = X.extents bl := by
  have hk : r'.nv.isLeaf' = r.nv.isLeaf' := hlf'.trans hlf.symm
  refine extents_congr hB (setNode_bs_self hB) (setNode_rootPid hB bl) (setNode_fuel hB)
    (by rw [setNode_v]) ?_ ?_
  · intro pid
    rw [setNode_ltree hB hk]
    by_cases h : resolve B pid = some l
    · rw [if_pos ⟨rfl, h⟩]
      unfold ltree
      rw [hB]; simp only; rw [h]; simp only [hr, Option.map_some, hlf, Write.shp]
    · rw [if_neg (fun e => h e.2)]
  · intro pid
    unfold Write.posIdOf
    show (match resolve B pid with
      | some y => (((B.ns.insert l r') !! y).map fun (x : NRec) => x.nv.pgid').getD 0
      | none => pid) = _
    cases h : resolve B pid with
    | none => rfl
    | some y =>
      simp only
      by_cases e : y = l
      · subst e; rw [GMap.lookup_insert, hr]; simp only [Option.map_some, Option.getD_some, hpg]
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]

/-- The page a materialization reads has the position's id (`Write.nodeAdded_pgid` from the
bucket's `bktClean`). -/
theorem nodeAdded_pgid_clean {X : WX} {bl : Loc} {B : BRec} {pgid : w64} {parent pa : Loc}
    {pg : List w8} (hc : bktClean X.v X.t.mv.pgid'.toNat bl B) (hB : X.t.bs !! bl = some B)
    (hpos : matPos X bl pgid parent) (hpg : wpageAt X.v B pgid = some (pa, pg))
    (hin : B.ib.root' ≠ W64 0) : (pageHdr pg).id' = pgid := by
  have hpg' : X.v.pages !! pgid.toNat = some pg := by
    unfold wpageAt at hpg; rw [if_neg hin] at hpg
    cases h : X.v.pages !! pgid.toNat with
    | none => rw [h] at hpg; cases hpg
    | some pg' => rw [h] at hpg; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpg
                  rw [hpg.2]
  have htw : treeWF X.v.pages X.t.mv.pgid'.toNat pgid.toNat := by
    obtain ⟨B1, hB1, hp⟩ := hpos
    rw [hB] at hB1; cases hB1
    rcases hp with ⟨-, hrn, rfl⟩ | ⟨i, r, w, hr, hleaf, hw, hwp, hnm⟩
    · exact (hc.2.1 hin).2 hrn
    · have hn := hc.2.2.2.2.2.2.2.1 parent r hr
      have hb := hn.2.2.2.2.2.2.2.2.2.2.2.2.1 hleaf
      have := (hb.2.2 w (List.mem_of_getElem? hw)).2.2
      rw [hwp] at this; exact this hnm
  cases htw with
  | page root pg2 h2 hlt hp hid hlen hptw =>
    rw [hpg'] at hp; cases hp
    apply BitVec.eq_of_toNat_eq
    exact hid

/-- **A materialization keeps the bucket's extents.** -/
theorem extents_nodeAdded {X Y : WX} {bl l : Loc} {pgid : w64} {parent : Loc}
    (hbl : bktLocalOK X bl) (h0 : ∀ B, X.t.bs !! bl = some B → B.ib.root' ≠ W64 0)
    (hadd : nodeAdded X Y bl l pgid parent) (hpos : matPos X bl pgid parent) :
    Y.extents bl = X.extents bl := by
  have hm : matGrow X Y bl := matGrow.step X Y Y bl l pgid parent hadd hpos (matGrow.refl Y bl)
  obtain ⟨-, hv, -, -, hlt⟩ := matGrow_keep hm hbl h0
  obtain ⟨-, -, -, -, -, -, -, -, -, hfuel⟩ := matGrow_frame hm
  have hf := matFresh_of_local hbl hadd h0
  obtain ⟨-, Bc, hBc, hcl, -⟩ := hbl
  obtain ⟨B, pa, pg, r, ns', bv', hB, hpg, hnm, -, -, -, -, hrid, -, -, -, -, -, -, -, -, -, -, -,
    -, hcase, hX'⟩ := hadd
  rw [hBc] at hB; cases hB
  have hin := h0 Bc hBc
  have hfnm := (hf Bc hBc).1
  have hB' : Y.t.bs !! bl = some { Bc with nm := Bc.nm.insert pgid l, ns := ns', bv := bv' } := by
    rw [hX']; simp
  have hns_pg : ∀ l0, l0 ≠ l →
      (ns' !! l0).map (fun r => r.nv.pgid') = (Bc.ns !! l0).map (fun r => r.nv.pgid') := by
    intro l0 hl0'
    rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', hrpp, -, -, -, -, -, -, -, hnv, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hl0')]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hl0')]
      by_cases hp : parent = l0
      · subst hp; rw [GMap.lookup_insert, hrpp]; simp only [Option.map_some, Option.some.injEq]
        rw [hnv]
      · rw [GMap.lookup_insert_ne _ _ hp]
  refine extents_congr hBc hB' ?_ hfuel (by rw [hv]) (fun pid => Write.shp_of_ldat _ _ (hlt pid)) ?_
  · unfold WX.rootPid; rw [hB', hBc]; rfl
  · intro pid
    unfold Write.posIdOf resolve
    simp only [hin, ↓reduceIte]
    by_cases hp : pid = pgid
    · subst hp
      rw [GMap.lookup_insert, hnm]
      simp only
      have : ns' !! l = some r := by
        rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', -, -, -, -, -, -, -, -, -, rfl⟩ <;> simp
      rw [this]
      simp only [Option.map_some, Option.getD_some, hrid]
      exact nodeAdded_pgid_clean hcl hBc hpos hpg hin
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hp)]
      cases hc : Bc.nm !! pid with
      | none => rfl
      | some l0 =>
        simp only
        have : l0 ≠ l := by intro e; subst e; exact hfnm pid hc
        rw [hns_pg l0 this]

/-- **Materializations keep the bucket's extents.** -/
theorem extents_matGrow {X Y : WX} {bl : Loc} (h : matGrow X Y bl) :
    bktLocalOK X bl → (∀ B, X.t.bs !! bl = some B → B.ib.root' ≠ W64 0) →
    Y.extents bl = X.extents bl := by
  induction h with
  | refl => intro _ _; rfl
  | step X Y Z bl l pgid parent hadd hpos hm ih =>
    intro hbl h0
    have hY := extents_nodeAdded hbl h0 hadd hpos
    obtain ⟨hblY, -, -, hibY, -⟩ :=
      matGrow_keep (matGrow.step X Y Y bl l pgid parent hadd hpos (matGrow.refl Y bl)) hbl h0
    rw [← hY]
    apply ih hblY
    intro B hB
    obtain ⟨Bx, hBx⟩ := Option.isSome_iff_exists.1 (show (X.t.bs !! bl).isSome by
      obtain ⟨-, B, hB, -⟩ := hbl; rw [hB]; rfl)
    obtain ⟨B', hB', hib⟩ := hibY Bx hBx
    rw [hB] at hB'; cases hB'
    rw [hib]; exact h0 Bx hBx

end extmat

end Spill

end bbolt
end EtcdGrove
end Perennial
