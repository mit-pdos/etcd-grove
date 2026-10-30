/-
What `b.node(pgid, parent)` (`nodeRes`) keeps beyond the nodes' pages (`NodePages.lean`): the
heights of the bucket's nodes and of the view's pages (`rblHt`: a node read from its page gets
its page's height) and the old nodes' entries and kind (only a parent's children list changes).
-/
module

public import Proof.go_etcd_io.bbolt.NodePages
public import Proof.go_etcd_io.bbolt.RebalanceDefs
public import Proof.go_etcd_io.bbolt.ShapeMat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The old nodes after `parentAdd`: the same entries and kind. -/
theorem spParentAdd_keep (ns : GMap Loc NRec) (parent l : Loc) (cs' : GoSlice) (y : Loc)
    (ry : NRec) (h : ns !! y = some ry) :
    ∃ r', (parentAdd ns parent l cs') !! y = some r' ∧ r'.ws = ry.ws ∧
      r'.nv.isLeaf' = ry.nv.isLeaf' := by
  unfold parentAdd
  split
  · exact ⟨ry, h, rfl, rfl⟩
  · split
    · rename_i rp hrp
      by_cases hy : y = parent
      · subst hy
        rw [hrp] at h; cases h
        exact ⟨_, GMap.lookup_insert _ _ _, rfl, rfl⟩
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hy)]
        exact ⟨ry, h, rfl, rfl⟩
    · exact ⟨ry, h, rfl, rfl⟩

/-- `b.node` keeps the old nodes' entries and kind. -/
theorem spNodeRes_keepN (B : BRec) (bl : Loc) (pgid : w64) (parent p : Loc) (pg : List w8)
    (src : Src) (l : Loc) (B' : BRec) (st st' : go_etcd_io.bbolt.TxStats)
    (hres : nodeRes B bl pgid parent p pg src l B' st st') :
    ∀ y ry, B.ns !! y = some ry → ∃ r', B'.ns !! y = some r' ∧ r'.ws = ry.ws ∧
      r'.nv.isLeaf' = ry.nv.isLeaf' := by
  intro y ry hy
  rcases hres with ⟨-, rfl, -⟩ | ⟨-, hl, -, -, s, cs', src', -, -, rfl⟩
  · exact ⟨ry, hy, rfl, rfl⟩
  · have hyl : y ≠ l := by intro e; subst e; rw [hl] at hy; cases hy
    obtain ⟨r', h1, h2, h3⟩ := spParentAdd_keep B.ns parent l cs' y ry hy
    refine ⟨r', ?_, h2, h3⟩
    show (<[l := _]> (parentAdd B.ns parent l cs')) !! y = some r'
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hyl)]; exact h1

/-- The old nodes of `B` are nodes of `B'` with the same entries and kind. -/
def spKeepE (B B' : BRec) : Prop :=
  ∀ l r, B.ns !! l = some r → ∃ r', B'.ns !! l = some r' ∧ r'.ws = r.ws ∧
    r'.nv.isLeaf' = r.nv.isLeaf'

theorem spKeepE_refl (B : BRec) : spKeepE B B := fun l r h => ⟨r, h, rfl, rfl⟩

theorem spKeepE_trans (B1 B2 B3 : BRec) (h1 : spKeepE B1 B2) (h2 : spKeepE B2 B3) :
    spKeepE B1 B3 := by
  intro l r h
  obtain ⟨r2, h2', a2, b2⟩ := h1 l r h
  obtain ⟨r3, h3, a3, b3⟩ := h2 l r2 h2'
  exact ⟨r3, h3, a3.trans a2, b3.trans b2⟩

/-- `b.node` keeps the heights (`rblHt`): the new node gets its page's. -/
theorem spRblHt_nodeRes (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (pm : GMap w64 Loc) (pgid : w64) (parent p : Loc) (pg : List w8) (src : Src) (l : Loc)
    (B' : BRec) (st st' : go_etcd_io.bbolt.TxStats) (hc : bktClean W hwm bl B)
    (hpre : B.nm !! pgid = none → nodeSrcOK W B pm pgid p pg src ∧
      ((parent = null ∧ B.bv.rootNode' = null ∧ pgid = B.ib.root') ∨ ∃ i, pagePosAt B parent i pgid))
    (hres : nodeRes B bl pgid parent p pg src l B' st st') (hh : rblHt W B) : rblHt W B' := by
  rcases hres with ⟨-, rfl, -⟩ | ⟨hk, hl, -, -, s, cs', src', -, -, rfl⟩
  · exact hh
  obtain ⟨hsrc, hcase⟩ := hpre hk
  obtain ⟨hc1, hc2, hc3, -, hc5, hc6, hc7, hc8, -, hfree⟩ := hc
  obtain ⟨ht, pht, hph, hall⟩ := hh
  have hpgr : B.ib.root' ≠ W64 0 → W.pages !! uint.nat pgid = some pg ∧ W64 (pageId pg) = pgid :=
    fun hr => by
      obtain ⟨-, -, h3, -, h5, -⟩ := hsrc.2.2.2 (hc6 hr)
      exact ⟨h3, h5⟩
  have hwf : B.ib.root' ≠ W64 0 → treeWF W.pages hwm (uint.nat pgid) := by
    intro hr0
    rcases hcase with ⟨-, hrn, hpe⟩ | ⟨i, rp, w, hrp, hb, hw, hwp, hnm⟩
    · rw [hpe]; exact (hc2 hr0).2 hrn
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -⟩ := hc8 parent rp hrp
      obtain ⟨-, -, hkids⟩ := h12 hb
      obtain ⟨-, -, hcwf⟩ := hkids w (List.mem_of_getElem? hw)
      rw [← hwp]; exact hcwf (by rw [hwp]; exact hnm)
  have hnf : ∀ d, treeHas W.pages (uint.nat pgid) d → B.nm !! W64 (d : Int) = none := by
    rcases hcase with ⟨-, hrn, -⟩ | ⟨i, hpos⟩
    · intro d _; rw [(hc3 hrn).2]; rfl
    · exact hfree parent i pgid hpos
  have hbr : pageFlags pg ≠ leafPageFlag → B.ib.root' ≠ W64 0 := by
    intro hnl h0
    rcases hcase with ⟨-, hrn, -⟩ | ⟨i, rp, w, hrp, hb, -⟩
    · obtain ⟨hpn, -, hg⟩ := hc1 h0 hrn
      obtain ⟨-, -, hpg, -⟩ := hsrc.2.2.1 hpn
      rw [hpg] at hnl; exact hnl (show inlineGood B.ipg from hg).2.1
    · have := hc7 h0 parent rp hrp; rw [hb] at this; cases this
  have hnml : ∀ c l', B.nm !! c = some l' → l' ≠ l := by
    intro c l' h e
    obtain ⟨-, r, hr, -⟩ := hc5 c l' h
    rw [e, hl] at hr; cases hr
  refine ⟨fun y => if y = l then (if B.ib.root' = W64 0 then 0 else pht (uint.nat pgid)) else ht y,
    pht, hph, fun y ry hy => ?_⟩
  change (<[l := readNRec bl parent p pg s src']> (parentAdd B.ns parent l cs')) !! y = some ry at hy
  show (ry.nv.isLeaf' = true → _ = 0) ∧ (ry.nv.isLeaf' = false → ∀ w ∈ ry.ws,
    (∀ l', (<[pgid := l]> B.nm) !! w.pgid = some l' → _ + 1 = _) ∧
    ((<[pgid := l]> B.nm) !! w.pgid = none → _))
  by_cases hyl : y = l
  · subst y
    rw [GMap.lookup_insert] at hy; cases hy
    dsimp only
    refine ⟨fun hlf => ?_, fun hlf w hw => ?_⟩
    · have hfl : pageFlags pg = leafPageFlag := by simpa [readNRec, readNodeV] using hlf
      rw [if_pos rfl]
      by_cases hr : B.ib.root' = W64 0
      · rw [if_pos hr]
      · rw [if_neg hr]; exact (hph _ pg (hpgr hr).1).1 hfl
    · have hnl : pageFlags pg ≠ leafPageFlag := by
        intro h; simp [readNRec, readNodeV, h] at hlf
      have hr := hbr hnl
      obtain ⟨hpg1, -⟩ := hpgr hr
      obtain ⟨-, -, -, hk2⟩ := treeWF_page _ _ _ pg (hwf hr) hpg1
      rcases hk2 with ⟨h, -⟩ | ⟨hbf, -, hkid⟩
      · exact absurd h hnl
      obtain ⟨i, hi, rfl⟩ := pageWs_mem pg src' w hw
      have hpw : (pageW pg src' i).pgid = W64 (branchPgid pg i : Int) := by
        unfold pageW; rw [if_neg hnl]
      have hclt : branchPgid pg i < 2 ^ 64 := by
        have := leAt_lt pg (elemOff i + 8) 8; unfold branchPgid; omega
      obtain ⟨cpg, hcpg⟩ : ∃ cpg, W.pages !! branchPgid pg i = some cpg := by
        cases hkid i hi with
        | page _ cpg _ h _ _ => exact ⟨cpg, h⟩
      have hne : branchPgid pg i ≠ uint.nat pgid :=
        child_ne_self W hv _ pg hpg1 hbf i hi (by rw [hcpg]; rfl)
      have hnmc : B.nm !! W64 (branchPgid pg i : Int) = none :=
        hnf _ (treeHas_child _ _ pg hpg1 hbf i hi _ (treeHas_self _ _ cpg hcpg))
      have hne' : W64 (branchPgid pg i : Int) ≠ pgid := by
        intro e; apply hne; rw [← e, uint_nat_W64_w _ hclt]
      have hnm' : (<[pgid := l]> B.nm) !! W64 (branchPgid pg i : Int) = none := by
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hne')]; exact hnmc
      rw [hpw]
      refine ⟨fun l' h => ?_, fun _ => ?_⟩
      · rw [hnm'] at h; cases h
      · rw [if_pos rfl, if_neg hr, uint_nat_W64_w _ hclt]
        exact (hph _ pg hpg1).2 hbf i hi
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hyl)] at hy
    obtain ⟨r0, h0, e1, -, e3, -⟩ := npg_parentAdd B.ns parent l cs' y ry hy
    obtain ⟨a1, a2⟩ := hall y r0 h0
    dsimp only
    rw [if_neg hyl]
    refine ⟨fun h => a1 (e3 ▸ h), fun h w hw => ?_⟩
    rw [e1] at hw
    have hbr0 : r0.nv.isLeaf' = false := e3 ▸ h
    obtain ⟨b1, b2⟩ := a2 hbr0 w hw
    have hr0 : B.ib.root' ≠ W64 0 := by
      intro hz; have := hc7 hz y r0 h0; rw [hbr0] at this; cases this
    by_cases hwp : w.pgid = pgid
    · rw [hwp]
      rw [hwp] at b2
      refine ⟨fun l' h' => ?_, fun h' => ?_⟩
      · rw [GMap.lookup_insert] at h'; cases h'
        rw [if_pos rfl, if_neg hr0]; exact b2 hk
      · rw [GMap.lookup_insert] at h'; cases h'
    · have hnmw : (<[pgid := l]> B.nm) !! w.pgid = B.nm !! w.pgid :=
        GMap.lookup_insert_ne _ _ (Ne.symm hwp)
      refine ⟨fun l' h' => ?_, fun h' => ?_⟩
      · rw [hnmw] at h'
        rw [if_neg (hnml _ _ h')]; exact b1 l' h'
      · rw [hnmw] at h'; exact b2 h'


end pure

end bbolt
end EtcdGrove
end Perennial
