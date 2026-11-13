/-
`Bucket.spill`'s root loop (U9x3, `notes/bbolt-proof-plan.md`): **the root bucket's page positions
lie under its positions at the start** (`rootUnder`, `RInv.rootPos`). A position of the root
bucket during the loop is a position at the start (`B0`) or a child page of a branch page below
one (`ownTo`, through branches only); materializations (`rootUnder_nodeAdded`: the new node's
children are its page's), a put into a leaf (`rootUnder_setLeaf`) and a child's spill
(`rootUnder_sim`) keep it. With `posShape` at the start it gives the shape of every page the
loop's searches read (`BktLoopPureRPut.rootPage_shape`); the branch keys by exact branch keys
(`treeKeys_keyLe`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTreeFrame
public import Proof.go_etcd_io.bbolt.Write.MatOK
public import Proof.go_etcd_io.bbolt.Read.WOpenOK
public import Proof.go_etcd_io.bbolt.Rebalance.RTreeX

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section rootpos
variable [GooseExts]

/-- `c` is `c0` or a child page of a branch page below `c0` (through branches). -/
def ownTo (P : Pages) (c0 c : Nat) : Prop :=
  c = c0 ∨ ∃ p pg j, ownHas P c0 p ∧ P !! p = some pg ∧ pageFlags pg = branchPageFlag ∧
    j < pageCount pg ∧ branchPgid pg j = c

/-- **Every page position of `B` is under one of `B0`'s.** -/
def rootUnder (P : Pages) (B0 B : BRec) : Prop :=
  ∀ c, posRoot B c → ∃ c0, posRoot B0 c0 ∧ ownTo P c0 c

theorem rp_cast_toNat {p : Nat} (h : p < 2 ^ 64) : (W64 (p : Int)).toNat = p := by
  simp only [BitVec.toNat_ofInt]; omega

theorem ownTo_ownHas {P : Pages} {c0 c : Nat} {pg : List w8} (h : ownTo P c0 c)
    (hpg : P !! c = some pg) : ownHas P c0 c := by
  rcases h with rfl | ⟨p, pgp, j, ho, hp, hf, hj, rfl⟩
  · exact ownHas.root _ pg hpg
  · exact WOpen.ownHas_snoc P ho pgp hp hf j hj pg hpg

theorem rootUnder_refl (P : Pages) (B0 : BRec) : rootUnder P B0 B0 :=
  fun c h => ⟨c, h, Or.inl rfl⟩

/-- A page position's tree is well-formed (`bktClean`). -/
theorem posRoot_treeWF {v : View} {hwm : Nat} {bl : Loc} {B : BRec} {c : Nat}
    (hcl : bktClean v hwm bl B) (h : posRoot B c) : treeWF v.pages hwm c := by
  rcases h with ⟨hrn, h0, rfl⟩ | ⟨l, i, ⟨r, w, hr, hlf, hw, hwp, hnm⟩, hlt⟩
  · exact (hcl.2.1 h0).2 hrn
  · have hn := hcl.2.2.2.2.2.2.2.1 l r hr
    have hb := hn.2.2.2.2.2.2.2.2.2.2.2.2.1 hlf
    have ht := (hb.2.2 w (List.mem_of_getElem? hw)).2.2 (by rw [hwp]; exact hnm)
    rw [hwp, rp_cast_toNat hlt] at ht
    exact ht

theorem wpageAt_page {v : View} {B : BRec} {pid : w64} {pa : Loc} {pg : List w8}
    (h0 : B.ib.root' ≠ W64 0) (h : wpageAt v B pid = some (pa, pg)) :
    v.pages !! pid.toNat = some pg := by
  unfold wpageAt at h
  rw [if_neg h0] at h
  cases hp : v.pages !! pid.toNat with
  | none => rw [hp] at h; cases h
  | some pg0 =>
    rw [hp] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]

/-- **A materialization's position is a position.** -/
theorem matPos_posRoot {X : WX} {bl : Loc} {pgid : w64} {parent : Loc} {B : BRec}
    (hpos : matPos X bl pgid parent) (hB : X.t.bs !! bl = some B) (h0 : B.ib.root' ≠ W64 0) :
    posRoot B pgid.toNat := by
  obtain ⟨B1, hB1, hp⟩ := hpos
  rw [hB] at hB1; cases hB1
  rcases hp with ⟨-, hrn, rfl⟩ | ⟨i, hpp⟩
  · exact Or.inl ⟨hrn, h0, rfl⟩
  · exact Or.inr ⟨parent, i, by rw [Write.w64_toNat_cast]; exact hpp, pgid.isLt⟩

/-- **A materialization keeps `rootUnder`** (its new node's children are its page's). -/
theorem rootUnder_nodeAdded {Y Y' : WX} {bl l : Loc} {pgid : w64} {parent : Loc} {B0 : BRec}
    {hwm : Nat} (hadd : nodeAdded Y Y' bl l pgid parent) (hpos : matPos Y bl pgid parent)
    (hcl : ∀ B, Y.t.bs !! bl = some B →
      bktClean Y.v hwm bl B ∧ B.ib.root' ≠ W64 0 ∧ rootUnder Y.v.pages B0 B) :
    ∀ B', Y'.t.bs !! bl = some B' → rootUnder Y'.v.pages B0 B' := by
  obtain ⟨B, pa, pg, r, ns', bv', hB, hwp, -, hl0, -, -, -, -, hlf, -, -, -, -, hdat, -, -,
    -, -, -, -, hcase, hX'⟩ := hadd
  obtain ⟨hc, h0, hU⟩ := hcl B hB
  have hpp := matPos_posRoot hpos hB h0
  obtain ⟨c0, hc0, hto⟩ := hU _ hpp
  have hpg := wpageAt_page h0 hwp
  have hown := ownTo_ownHas hto hpg
  subst hX'
  intro B' hB'
  have e : (Y.t.bs.insert bl { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' }) !! bl =
      some { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' } := GMap.lookup_insert _ _ _
  rw [show (Y.t.bs.insert bl _ : GMap Loc BRec) = _ from rfl, e] at hB'
  cases hB'
  show rootUnder Y.v.pages B0 _
  intro c hposc
  rcases hposc with ⟨hrn', h0', rfl⟩ | ⟨y, j, ⟨ry, w, hy, hylf, hw, hwp', hnm'⟩, hlt⟩
  · rcases hcase with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
    · exact absurd hrn' hl0
    · exact hU _ (Or.inl ⟨hrn', h0', rfl⟩)
  · have hnm : B.nm !! W64 (c : Int) = none := Write.nm_ins_none _ _ _ _ hnm'
    have hns' : ns' !! l = some r ∧ ∀ y ry, y ≠ l → ns' !! y = some ry →
        ∃ ry0, B.ns !! y = some ry0 ∧ ry.nv.isLeaf' = ry0.nv.isLeaf' ∧ ry.ws = ry0.ws := by
      rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', hrp, -, -, hws, -, -, -, -, hnv, rfl⟩
      · refine ⟨GMap.lookup_insert _ _ _, fun y ry hyl hy => ?_⟩
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hyl)] at hy
        exact ⟨ry, hy, rfl, rfl⟩
      · refine ⟨GMap.lookup_insert _ _ _, fun y ry hyl hy => ?_⟩
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hyl)] at hy
        by_cases ep : y = parent
        · subst ep
          rw [GMap.lookup_insert] at hy; cases hy
          exact ⟨rp, hrp, by rw [hnv], hws⟩
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm ep)] at hy
          exact ⟨ry, hy, rfl, rfl⟩
    by_cases hyl : y = l
    · subst hyl
      rw [hns'.1] at hy; cases hy
      have hnl : pageFlags pg ≠ leafPageFlag := by
        intro e; rw [hlf, e] at hylf; simp at hylf
      have hbr : pageFlags pg = branchPageFlag := by
        rcases posRoot_treeWF hc hpp with ⟨_, pg', _, _, hpg', _, _, hpt⟩
        rw [hpg] at hpg'; cases hpg'
        rcases mat_kind hpt with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd h hnl
        · exact h
      have hd : r.ws.map wDat = (pageWs pg).map wDat := hdat.trans (mat_pageWsAs_wDat pg _)
      obtain ⟨hj, hdw⟩ := mat_at hd j w hw
      have hpg' : w.pgid = W64 (branchPgid pg j : Int) := by
        rw [(mat_wDat_eq hdw).2.1, pageW_pgid_branch pg j hbr]
      have hcj : c = branchPgid pg j := by
        have := congrArg BitVec.toNat (hwp'.symm.trans hpg')
        rw [rp_cast_toNat hlt, rp_cast_toNat (Write.branchPgid_lt pg j)] at this
        exact this
      exact ⟨c0, hc0, Or.inr ⟨pgid.toNat, pg, j, hown, hpg, hbr, hj, hcj.symm⟩⟩
    · obtain ⟨ry0, hry0, e1, e2⟩ := hns'.2 y ry hyl hy
      refine hU c (Or.inr ⟨y, j, ⟨ry0, w, hry0, e1 ▸ hylf, e2 ▸ hw, hwp', hnm⟩, hlt⟩)

/-- **A put into a leaf keeps `rootUnder`.** -/
theorem rootUnder_setLeaf {P : Pages} {B0 B : BRec} {l : Loc} {r' : NRec}
    (hU : rootUnder P B0 B) (hlf : r'.nv.isLeaf' = true) :
    rootUnder P B0 { B with ns := B.ns.insert l r' } := by
  intro c h
  apply hU
  rcases h with h | ⟨y, j, ⟨ry, w, hy, hylf, hw, hwp, hnm⟩, hlt⟩
  · exact Or.inl h
  · by_cases e : y = l
    · subst e
      have hy' : (B.ns.insert y r') !! y = some ry := hy
      rw [GMap.lookup_insert] at hy'; cases hy'
      rw [hlf] at hylf; cases hylf
    · have hy' : (B.ns.insert l r') !! y = some ry := hy
      rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hy'
      exact Or.inr ⟨y, j, ⟨ry, w, hy', hylf, hw, hwp, hnm⟩, hlt⟩

/-- **A record equal modulo sources keeps `rootUnder`** (a child's spill, `bktKept`). -/
theorem rootUnder_sim {P : Pages} {B0 B B' : BRec} (hU : rootUnder P B0 B) (hs : bktSim B B')
    (hns : ∀ l, optRel nodeSim (B.ns !! l) (B'.ns !! l)) : rootUnder P B0 B' := by
  intro c h
  apply hU
  rcases h with ⟨hrn, h0, rfl⟩ | ⟨y, j, ⟨ry', w', hy, hylf, hw, hwp, hnm⟩, hlt⟩
  · refine Or.inl ⟨?_, ?_, ?_⟩
    · rw [← hs.1]; exact hrn
    · rw [← hs.2.1]; exact h0
    · rw [hs.2.1]
  · have h := hns y
    rw [hy] at h
    cases hry : B.ns !! y with
    | none => rw [hry] at h; exact absurd h (by simp [optRel])
    | some ry =>
      rw [hry] at h
      have h' : nodeSim ry ry' := h
      obtain ⟨w, hw0, hd⟩ := get_of_dat h'.2.2.1 hw
      refine Or.inr ⟨y, j, ⟨ry, w, hry, ?_, hw0, ?_, by rw [← hs.2.2.1]; exact hnm⟩, hlt⟩
      · have := congrArg (fun n => n.isLeaf') h'.1
        simp only at this; rw [← this]; exact hylf
      · rw [← (mat_wDat_eq hd).2.1]; exact hwp

/-- **Exact branch keys bound a tree's keys by its leaves'.** -/
theorem treeKeys_keyLe {P : Pages} {K c0 : Nat} :
    ∀ {p : Nat} {lo hi : Option (List w8)}, treeKeys P p lo hi → ownHas P c0 p →
      (∀ q qpg, ownHas P c0 q → P !! q = some qpg → pageFlags qpg = leafPageFlag →
        ∀ i < pageCount qpg, leafKsize qpg i ≤ K) →
      ∀ pg, P !! p = some pg → ∀ i < pageCount pg, (pageKey pg i).length ≤ K := by
  intro p lo hi h
  induction h with
  | leaf root pg0 lo hi hpg0 hfl _ _ _ =>
    intro _ hL pg hpg i hi
    rw [hpg0] at hpg; cases hpg
    rw [mat_pageKey_leaf _ _ hfl]
    unfold leafKey
    have := Write.bytesAt_length_le pg0 (elemOff i + leafPos pg0 i) (leafKsize pg0 i)
    have := hL root pg0 (by assumption) hpg0 hfl i hi
    omega
  | branch root pg0 lo hi kind hpg0 hfl _ _ hch _ ih =>
    intro hown hL pg hpg i hi
    rw [hpg0] at hpg; cases hpg
    rw [mat_pageKey_branch _ _ hfl]
    obtain ⟨cpg, hcpg, hc0, -, hk⟩ := hch i hi
    rw [← hk]
    exact ih i hi (WOpen.ownHas_snoc P hown pg0 hpg0 hfl i hi cpg hcpg) hL cpg hcpg 0 hc0

end rootpos

end Spill

end bbolt
end EtcdGrove
end Perennial
