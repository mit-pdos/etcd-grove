/-
`Bucket.spill`'s root loop (U9t, `notes/bbolt-proof-plan.md`): **`child.free()`'s premise** for an
inlineable child (`rinv_freePre'`, `BktLoopStep.rinv_freePre`'s proof). The child's root node is a
leaf, so its only position is its root page and its only extent the leaf's own page, whose slots
the child owns (`Dc k`, in the slot invariant: neither free nor pending) and which is no allocation
of the writer (`spFree`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopInv
public import Proof.go_etcd_io.bbolt.Spill.BktPm

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section free
variable [GooseExts]

/-- Distinct ids below `n` number at most `n`. -/
theorem length_le_of_nodup_lt' (l : List w64) (n : Nat) (hnd : l.Nodup)
    (hlt : ∀ x ∈ l, x.toNat < n) : l.length ≤ n := by
  have hnd' : (l.map BitVec.toNat).Nodup :=
    List.Pairwise.map BitVec.toNat (fun a b hab h => hab (BitVec.eq_of_toNat_eq h)) hnd
  have hsub : l.map BitVec.toNat ⊆ List.range n := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact List.mem_range.2 (hlt x hx)
  have := (List.subperm_of_subset hnd' hsub).length_le
  simpa using this

/-- **The positions of a bucket whose root node is a leaf**: its root page alone. -/
theorem positions_leafRoot {X : WX} {c : Loc} {C : BRec} {rn : NRec}
    (hC : X.t.bs !! c = some C) (hres : resolve C C.ib.root' = some C.bv.rootNode')
    (hns : C.ns !! C.bv.rootNode' = some rn) (hleaf : rn.nv.isLeaf' = true) :
    X.positions c = [C.ib.root'] := by
  unfold WX.positions WX.fuel
  have hr : X.rootPid c = C.ib.root' := by unfold WX.rootPid; rw [hC]; rfl
  rw [hr]
  unfold lposF
  have hl : ltree X c C.ib.root' = some (true, rn.ws) := by
    unfold ltree; rw [hC]; simp only; rw [hres]; simp only; rw [hns]; simp [hleaf]
  rw [hl]

/-- **`child.free()`'s premise** (see the module doc). -/
theorem rinv_freePre' {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k : GoString} {c : Loc}
    {C : BRec} {rn : NRec} (hks : ks k = .todo) (hc : B0.bm !! k = some c)
    (hC : X.t.bs !! c = some C) (hrn : X.node c C.bv.rootNode' = some rn)
    (hleaf : rn.nv.isLeaf' = true) :
    C.ib.root' ≠ W64 0 → bktLocalOK X c ∧ (∀ pid ∈ X.positions c, X.t.pm !! pid = none) ∧
      w.fl.canFreeAll w.wtxid (X.extents c) ∧ rtOK X c ∧ X.t.mv.txid' = w.wtxid := by
  intro h0
  have hkid := hI.kids k c hc
  rw [hks] at hkid
  obtain ⟨C', hC', -, -, -, hloc, hrt, -, -, htree⟩ := hkid
  rw [hC] at hC'; cases hC'
  have hwx : w.wtxid = w0.wtxid := wtxid_of_C hI.C
  have hG := hI.G
  have htx : X.t.mv.txid' = w.wtxid := by rw [hwx]; exact hG.1
  have hns : C.ns !! C.bv.rootNode' = some rn := by
    unfold WX.node at hrn; rw [hC] at hrn; exact hrn
  have hnn : C.bv.rootNode' ≠ null := by
    intro e
    have := (hG.2.2.1.2.2.1 c C hC).2
    rw [e] at hns; rw [this] at hns; cases hns
  have hloc' := hloc hnn
  obtain ⟨-, B', hB', hcl, -⟩ := hloc'
  rw [hC] at hB'; cases hB'
  refine ⟨hloc hnn, positions_pm_none hG hC hcl h0 hrt, ?_, hrt, htx⟩
  obtain ⟨rn', h, F, N, E, hrn', -, hu, hfr, -⟩ := htree hnn
  rw [hrn] at hrn'; cases hrn'
  have hres : resolve C C.ib.root' = some C.bv.rootNode' := by
    unfold resolve; rw [if_neg h0]; exact hcl.2.2.2.1 hnn
  have hpos := positions_leafRoot hC hres hns hleaf
  -- the leaf's own page and slots
  have hleafU : F = ownF rn.nv.pgid' ∧ (∀ s ∈ ownSl X.v rn.nv.pgid', s ∈ Dc k) ∧
      ownPg X.v rn.nv.pgid' := by
    generalize hD : Dc k = D at hu
    cases hu with
    | leaf _ r _ _ _ hr hu' =>
      rw [hrn] at hr; cases hr
      exact ⟨rfl, fun s hs => List.mem_append_left _ hs, hu'.2.2.2.2.2.2.2⟩
    | branch _ r _ _ _ _ hr _ hl =>
      rw [hrn] at hr; cases hr; rw [hleaf] at hl; cases hl
  obtain ⟨hF, hsl, hown⟩ := hleafU
  have hext : X.extents c = (X.posExtent c C.ib.root').toList := by
    unfold WX.extents; rw [hpos]
    cases h : X.posExtent c C.ib.root' <;> simp [h]
  rw [hext]
  unfold WX.posExtent
  rw [hC]; simp only; rw [hres]; simp only; rw [hns]
  simp only [Option.map_some, Option.getD_some]
  by_cases hp0 : rn.nv.pgid' = W64 0
  · rw [if_pos hp0]; trivial
  rw [if_neg hp0]
  obtain ⟨pg, hpg, -, -, -, h2, hb⟩ := hown hp0
  rw [hpg]
  simp only [Option.map_some, Option.toList_some]
  refine ⟨?_, trivial⟩
  -- the extent's slots are owned
  have hkm : k ∈ keys := hI.keysAll k (by rw [hc]; rfl)
  have hown' : ∀ j < 1 + pageOverflow pg, rn.nv.pgid'.toNat + j ∈ Lroot ++ keys.flatMap Dc := by
    intro j hj
    have : rn.nv.pgid'.toNat + j ∈ ownSl X.v rn.nv.pgid' := by
      unfold ownSl pgSlots; rw [if_neg hp0]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [hpg]; exact List.mem_range'_1.2 ⟨by omega, by omega⟩
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨k, hkm, hsl _ this⟩)
  obtain ⟨-, hL, hnd2, hlt⟩ := hI.slots
  have hm62 := hG.2.2.2.2.2.2.1
  have hn : rn.nv.pgid'.toNat + (1 + pageOverflow pg) < 2 ^ 64 := by omega
  refine ⟨h2, hn, ?_, ?_, ?_⟩
  · intro x hx hxa
    obtain ⟨a1, a2⟩ := (mem_runIds hn).1 hx
    have hs := hown' (x.toNat - rn.nv.pgid'.toNat) (by omega)
    have he : rn.nv.pgid'.toNat + (x.toNat - rn.nv.pgid'.toNat) = x.toNat := by omega
    rw [he] at hs
    have := (hL _ hs).2.2
    rw [show W64 (x.toNat : Int) = x from by
      apply BitVec.eq_of_toNat_eq; rw [w64_toNat_of_lt (by omega)]] at this
    exact this hxa
  · have hf := (hfr rn.nv.pgid'.toNat (by rw [hF]; unfold ownF; rw [if_neg hp0]; simp)).2
    rw [show W64 (rn.nv.pgid'.toNat : Int) = rn.nv.pgid' from by
      apply BitVec.eq_of_toNat_eq; rw [w64_toNat_of_lt (by omega)]] at hf
    rw [hwx]; exact hf
  · have := length_le_of_nodup_lt' _ (2 ^ 62) hnd2
      (fun x hx => by have := hlt x hx; omega)
    omega

end free

end Spill

end bbolt
end EtcdGrove
end Perennial
