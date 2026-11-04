/-
`Bucket.spill`'s initial trees (U9i, `notes/bbolt-proof-plan.md`), part 6: **the heights of a
clean bucket's nodes** (`nodeHts`): from its logical tree's finite tree (`rtOK`: leaves at one
depth, height below the fuel) and its nodes reached from its root node (`descIn`, `liveReach`),
a height function with `InitB`'s `hts` (a leaf `0`, a branch one more than its children, a page
child's height its page's), the root node's below the fuel.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktHt
public import Proof.go_etcd_io.bbolt.Spill.BktInit

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section nodes
variable [GooseExts]

variable {X : WX} {bl : Loc} {B : BRec} {C : CommitSt} {pht : Nat → Nat}
  {bnd : Loc → Option (List w8) × Option (List w8)}

/-- The premises of `nodeHts` (`InitB`'s but the heights, and the finite tree). -/
structure HtB (X : WX) (bl : Loc) (B : BRec) (C : CommitSt) (pht : Nat → Nat)
    (bnd : Loc → Option (List w8) × Option (List w8)) : Prop where
  hB : X.t.bs !! bl = some B
  clean : bktClean X.v X.t.mv.pgid'.toNat bl B
  keys : bktKeysB X.v B bnd
  ne2 : ∀ l r, B.ns !! l = some r → r.nv.isLeaf' = false → 2 ≤ r.ws.length
  cpages : X.v.pages = C.pages
  hpht : pageHts C.pages pht
  rn : B.bv.rootNode' ≠ null
  reach : ∀ l r, B.ns !! l = some r → descIn B B.bv.rootNode' l
  rt : rtOK X bl

theorem HtB.nc (H : HtB X bl B C pht bnd) {l : Loc} {r : NRec} (hr : B.ns !! l = some r) :
    nodeClean X.v X.t.mv.pgid'.toNat bl B l r := H.clean.2.2.2.2.2.2.2.1 l r hr

theorem HtB.ltree_node (H : HtB X bl B C pht bnd) {l : Loc} {r : NRec} {pid : w64}
    (hr : B.ns !! l = some r) (hres : resolve B pid = some l) :
    ltree X bl pid = some (r.nv.isLeaf', r.ws) := by
  unfold ltree; rw [H.hB]; simp only; rw [hres]; simp only [hr, Option.map_some]

theorem HtB.root_ne (H : HtB X bl B C pht bnd) {l : Loc} {r : NRec}
    (hr : B.ns !! l = some r) (hl : r.nv.isLeaf' = false) : B.ib.root' ≠ W64 0 := by
  intro h0
  have := H.clean.2.2.2.2.2.2.1 h0 l r hr
  rw [hl] at this; cases this

theorem HtB.ltree_pages (H : HtB X bl B C pht bnd) {l : Loc} {r : NRec} {i : Nat}
    {w : WEntry} (hr : B.ns !! l = some r) (hl : r.nv.isLeaf' = false) (hw : r.ws[i]? = some w)
    (hnm : B.nm !! w.pgid = none) :
    ∀ q : w64, treeHas C.pages w.pgid.toNat q.toNat →
      ltree X bl q = (C.pages !! q.toNat).map pgRead := by
  intro q hq
  have h0 := H.root_ne hr hl
  have hpos : pagePosAt B l i w.pgid := ⟨r, w, hr, hl, hw, rfl, hnm⟩
  have hq' : treeHas X.v.pages w.pgid.toNat q.toNat := by rw [H.cpages]; exact hq
  have hfree := H.clean.2.2.2.2.2.2.2.2.2 l i w.pgid hpos q.toNat hq'
  rw [show W64 (q.toNat : Int) = q by simp] at hfree
  unfold ltree; rw [H.hB]; simp only
  have hres : resolve B q = none := by unfold resolve; rw [if_neg h0]; exact hfree
  rw [hres]; simp only
  unfold wpageAt; rw [if_neg h0, Option.map_map, H.cpages]; rfl

/-- A node with a child is a branch. -/
theorem HtB.branch_of_child (H : HtB X bl B C pht bnd) {l : Loc} {r : NRec} {c : Loc}
    (hr : B.ns !! l = some r) (hc : c ∈ r.cs) : r.nv.isLeaf' = false ∧ ∃ rc,
      B.ns !! c = some rc ∧ rc.nv.parent' = l ∧ ∃ (i : Nat) (w : WEntry), r.ws[i]? = some w ∧
        w.pgid = rc.nv.pgid' := by
  obtain ⟨rc, hrc, hpc⟩ := (H.nc hr).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 c hc
  have hl0 : l ≠ null := (H.clean.2.2.2.2.1 _ l (H.nc hr).2.2.2.2.2.2.2.1).1
  have hpn : rc.nv.parent' ≠ null := by rw [hpc]; exact hl0
  obtain ⟨rp, hrp, hpl, -⟩ := (H.nc hrc).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpn
  rw [hpc, hr] at hrp; cases hrp
  obtain ⟨-, rp, i, w, hrp, hwi, hwp, -⟩ := (H.keys.2.2 c rc hrc).2.2.1 hpn
  rw [hpc, hr] at hrp; cases hrp
  exact ⟨hpl, rc, hrc, hpc, i, w, hwi, hwp⟩

/-- A materialized node's position resolves to it. -/
theorem HtB.resolve_node (H : HtB X bl B C pht bnd) {l : Loc} {r : NRec}
    (hr : B.ns !! l = some r) (h0 : B.ib.root' ≠ W64 0) : resolve B r.nv.pgid' = some l :=
  resolve_nm h0 (H.nc hr).2.2.2.2.2.2.2.1

theorem HtB.t_root (H : HtB X bl B C pht bnd) {t : RTree} (hp : t.pid = X.rootPid bl) :
    resolve B t.pid = some B.bv.rootNode' := by
  have hrp : X.rootPid bl = B.ib.root' := by simp only [WX.rootPid, H.hB, Option.map_some, Option.getD_some]
  rw [hp, hrp]
  unfold resolve
  split
  · rw [if_neg H.rn]
  · exact H.clean.2.2.2.1 H.rn

/-- A child of a node at a position of the finite tree is at one too. -/
theorem HtB.inT_child (H : HtB X bl B C pht bnd) {t : RTree} (ht : ltIs (ltree X) bl t)
    {n c : Loc} {rn : NRec} (hrn : B.ns !! n = some rn) (hc : c ∈ rn.cs) {k : Nat} {s : RTree}
    (hs : subT t k s) (hres : resolve B s.pid = some n) :
    ∃ k s, subT t k s ∧ resolve B s.pid = some c := by
  obtain ⟨hlf, rc, hrc, -, i, w, hwi, hwp⟩ := H.branch_of_child hrn hc
  have hls := subT_ltIs ht hs
  obtain ⟨p, b, ws, cs⟩ := s
  obtain ⟨hL, -, hbr⟩ := ltIs_mk hls
  simp only [RTree.pid] at hres
  rw [H.ltree_node hrn hres] at hL
  simp only [Option.some.injEq, Prod.mk.injEq] at hL
  obtain ⟨hb, hws⟩ := hL
  rw [hlf] at hb; subst hb; subst hws
  have g := ltIsL_get (hbr rfl)
  have hi : i < cs.length := by rw [g.1]; exact (List.getElem?_eq_some_iff.1 hwi).1
  obtain ⟨w', hw', hcp, -⟩ := g.2 i cs[i] (List.getElem?_eq_getElem hi)
  rw [hwi] at hw'; cases hw'
  refine ⟨k + 1, cs[i], subT.child k p rn.ws cs cs[i] hs (List.getElem_mem hi), ?_⟩
  rw [hcp, hwp]
  exact H.resolve_node hrc (H.root_ne hrn hlf)

/-- **Every node is at a position of the finite tree.** -/
theorem HtB.inT (H : HtB X bl B C pht bnd) {t : RTree} (ht : ltIs (ltree X) bl t)
    (hp : t.pid = X.rootPid bl) {l : Loc} (hd : descIn B B.bv.rootNode' l) :
    ∃ k s, subT t k s ∧ resolve B s.pid = some l := by
  have key : ∀ a d, descIn B a d → (∃ k s, subT t k s ∧ resolve B s.pid = some a) →
      ∃ k s, subT t k s ∧ resolve B s.pid = some d := by
    intro a d h
    induction h with
    | self => exact id
    | child n c d rn hrn hc _ ih =>
      rintro ⟨k, s, hs, hres⟩
      exact ih (H.inT_child ht hrn hc hs hres)
  exact key _ _ hd ⟨0, t, subT.refl, H.t_root hp⟩

end nodes

end Spill

end bbolt
end EtcdGrove
end Perennial
