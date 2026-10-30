/-
What a write transaction's nodes keep of the pages they were read from, before `Commit`
(`bktPg`, a conjunct of `txShape`, `WriteTxShape.lean`): bbolt modifies only leaves before
`Commit` (`Put`, `Delete` and `CreateBucket` change a leaf's entries), so

- a branch node's entries are its page's (their children's page ids, and its key is its first
  entry's), and its page is a branch page of the view;
- a leaf node of a bucket stored in pages was read from a leaf page of the view;
- a leaf's entries have no child page (`pgid` 0: a page leaf's entries are read with `W64 0`,
  `Put` and `CreateBucket` put entries with 0).

This is what gives the nodes heights (with the view's `pageHts`) and the branches their first
keys as lower bounds (`RebalanceReady.lean`). It is not part of the bucket-level shape
(`bktShape`), which must hold again after `rebalance` (whose merges change branches): the
bucket-level specs that materialize nodes (`Bucket.node.sspec`, `Cursor.node.sspec`) say that
they keep it (`bktPg_nodeRes`).
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxClean

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The node `r` of a bucket whose root page id is `root` and its page (see the module doc). -/
def nodePg (W : WView) (root : w64) (r : NRec) : Prop :=
  (r.nv.isLeaf' = true → (∀ w ∈ r.ws, w.pgid = W64 0) ∧
    (root ≠ W64 0 → ∃ pg, W.pages !! uint.nat r.nv.pgid' = some pg ∧ pageFlags pg = leafPageFlag)) ∧
  (r.nv.isLeaf' = false → r.key = wKey r.ws 0 ∧ ∃ pg, W.pages !! uint.nat r.nv.pgid' = some pg ∧
    pageFlags pg = branchPageFlag ∧ r.ws.length = pageCount pg ∧
    ∀ i w, r.ws[i]? = some w → w.pgid = W64 (branchPgid pg i))

/-- The nodes of the bucket `B` and their pages (see the module doc). -/
def bktPg (W : WView) (B : BRec) : Prop :=
  ∀ l r, B.ns !! l = some r → nodePg W B.ib.root' r

theorem bktPg_congr (W : WView) (B1 B2 : BRec) (hns : B1.ns = B2.ns)
    (hr : B1.ib.root' = B2.ib.root') : bktPg W B1 ↔ bktPg W B2 := by
  unfold bktPg; rw [hns, hr]

theorem bktPg_empty (W : WView) (B : BRec) (h : B.ns = ∅) : bktPg W B := by
  intro l r hl; rw [h] at hl; cases hl

/-- A leaf's record changed as by `Put`/`Delete`/`CreateBucket` (the entries `D` replaced by
`E`, with no child page). -/
theorem bktPg_leafOp (W : WView) (B : BRec) (hp : bktPg W B) (l : Loc) (r r' : NRec)
    (hr : B.ns !! l = some r) (hleaf : r.nv.isLeaf' = true)
    (A D C E : List WEntry) (hws : r.ws = A ++ D ++ C) (hws' : r'.ws = A ++ E ++ C)
    (hE : ∀ w ∈ E, w.pgid = W64 0)
    (e1 : r'.nv.isLeaf' = true) (e3 : r'.nv.pgid' = r.nv.pgid') :
    bktPg W { B with ns := <[l := r']> B.ns } := by
  intro y ry hy
  simp only at hy ⊢
  by_cases hyl : y = l
  · subst hyl
    rw [GMap.lookup_insert] at hy; cases hy
    obtain ⟨h1, -⟩ := hp y r hr
    obtain ⟨h0, hpg⟩ := h1 hleaf
    refine ⟨fun _ => ⟨fun w hw => ?_, fun h => by rw [e3]; exact hpg h⟩, fun h => by
      rw [e1] at h; cases h⟩
    rw [hws'] at hw
    simp only [List.mem_append] at hw
    rcases hw with (h | h) | h
    · exact h0 w (by rw [hws]; simp [h])
    · exact hE w h
    · exact h0 w (by rw [hws]; simp [h])
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hyl)] at hy
    exact hp y ry hy

/-- The old nodes after `parentAdd`: the same entries, key, kind and page. -/
theorem npg_parentAdd (ns : GMap Loc NRec) (parent l : Loc) (cs' : GoSlice) (y : Loc) (ry : NRec)
    (h : (parentAdd ns parent l cs') !! y = some ry) :
    ∃ r0, ns !! y = some r0 ∧ ry.ws = r0.ws ∧ ry.key = r0.key ∧ ry.nv.isLeaf' = r0.nv.isLeaf' ∧
      ry.nv.pgid' = r0.nv.pgid' := by
  unfold parentAdd at h
  split at h
  · exact ⟨ry, h, rfl, rfl, rfl, rfl⟩
  · split at h
    · rename_i rp hrp
      by_cases hy : y = parent
      · subst hy; rw [GMap.lookup_insert] at h; cases h
        exact ⟨rp, hrp, rfl, rfl, rfl, rfl⟩
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hy)] at h
        exact ⟨ry, h, rfl, rfl, rfl, rfl⟩
    · exact ⟨ry, h, rfl, rfl, rfl, rfl⟩

/-- What `b.node(pgid, parent)` did (`nodeRes`, under `Bucket.node.sspec`'s precondition)
keeps the nodes' pages: a new node is read from its page. -/
theorem bktPg_nodeRes (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (pm : GMap w64 Loc) (pgid : w64) (parent p : Loc) (pg : List w8) (src : Src) (l : Loc)
    (B' : BRec) (st st' : go_etcd_io.bbolt.TxStats) (hc : bktClean W hwm bl B)
    (hpre : B.nm !! pgid = none → nodeSrcOK W B pm pgid p pg src ∧
      ((parent = null ∧ B.bv.rootNode' = null ∧ pgid = B.ib.root') ∨ ∃ i, pagePosAt B parent i pgid))
    (hres : nodeRes B bl pgid parent p pg src l B' st st') (hp : bktPg W B) : bktPg W B' := by
  rcases hres with ⟨-, rfl, -⟩ | ⟨hk, -, -, -, s, cs', src', -, -, rfl⟩
  · exact hp
  obtain ⟨hsrc, hcase⟩ := hpre hk
  obtain ⟨hc1, hc2, -, -, -, hc6, hc7, hc8, -, -⟩ := hc
  -- the page of the new node
  have hpgr : B.ib.root' ≠ W64 0 → W.pages !! uint.nat pgid = some pg ∧ W64 (pageId pg) = pgid :=
    fun hr => by
      obtain ⟨-, -, h3, -, h5, -⟩ := hsrc.2.2.2 (hc6 hr)
      exact ⟨h3, h5⟩
  -- a branch page is in a bucket stored in pages, and is a well-formed tree's page
  have hbr : pageFlags pg ≠ leafPageFlag → B.ib.root' ≠ W64 0 ∧ pageFlags pg = branchPageFlag := by
    intro hnl
    have hr0 : B.ib.root' ≠ W64 0 := by
      intro h0
      rcases hcase with ⟨-, hrn, -⟩ | ⟨i, rp, w, hrp, hb, -⟩
      · obtain ⟨hpn, -, hg⟩ := hc1 h0 hrn
        obtain ⟨-, -, hpg, -⟩ := hsrc.2.2.1 hpn
        rw [hpg] at hnl; exact hnl (show inlineGood B.ipg from hg).2.1
      · have := hc7 h0 parent rp hrp; rw [hb] at this; cases this
    refine ⟨hr0, ?_⟩
    have hwf : treeWF W.pages hwm (uint.nat pgid) := by
      rcases hcase with ⟨-, hrn, hpe⟩ | ⟨i, rp, w, hrp, hb, hw, hwp, hnm⟩
      · rw [hpe]; exact (hc2 hr0).2 hrn
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -⟩ := hc8 parent rp hrp
        obtain ⟨-, -, hkids⟩ := h12 hb
        obtain ⟨-, -, hcwf⟩ := hkids w (List.mem_of_getElem? hw)
        rw [← hwp]; exact hcwf (by rw [hwp]; exact hnm)
    rcases (treeWF_page _ _ _ pg hwf (hpgr hr0).1).2.2.2 with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hnl
    · exact h
  intro y ry hy
  show nodePg W B.ib.root' ry
  change (<[l := readNRec bl parent p pg s src']> (parentAdd B.ns parent l cs')) !! y = some ry at hy
  by_cases hyl : y = l
  · subst hyl
    rw [GMap.lookup_insert] at hy; cases hy
    refine ⟨fun hlf => ?_, fun hlf => ?_⟩
    · have hfl : pageFlags pg = leafPageFlag := by
        simpa [readNRec, readNodeV] using hlf
      refine ⟨fun w hw => ?_, fun hr => ?_⟩
      · obtain ⟨j, -, rfl⟩ := pageWs_mem pg src' w hw
        unfold pageW; rw [if_pos hfl]
      · obtain ⟨h1, h2⟩ := hpgr hr
        refine ⟨pg, ?_, hfl⟩
        show W.pages !! uint.nat (W64 (pageId pg)) = some pg
        rw [h2]; exact h1
    · have hnl : pageFlags pg ≠ leafPageFlag := by
        intro h; simp [readNRec, readNodeV, h] at hlf
      obtain ⟨hr, hb⟩ := hbr hnl
      obtain ⟨h1, h2⟩ := hpgr hr
      refine ⟨rfl, pg, ?_, hb, pageWs_length pg src', fun i w hw => ?_⟩
      · show W.pages !! uint.nat (W64 (pageId pg)) = some pg
        rw [h2]; exact h1
      · change (pageWs pg src')[i]? = some w at hw
        rw [pageWs_get] at hw
        split at hw
        · cases hw; unfold pageW; rw [if_neg hnl]
        · cases hw
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hyl)] at hy
    obtain ⟨r0, h0, e1, e2, e3, e4⟩ := npg_parentAdd B.ns parent l cs' y ry hy
    obtain ⟨n1, n2⟩ := hp y r0 h0
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [e3] at h
      obtain ⟨a, b⟩ := n1 h
      exact ⟨by rw [e1]; exact a, by rw [e4]; exact b⟩
    · rw [e3] at h
      obtain ⟨a, b⟩ := n2 h
      rw [e1, e2, e4]; exact ⟨a, b⟩

/-- Every bucket of the transaction's buckets `bs` and its nodes' pages. -/
def txPg (W : WView) (bs : GMap Loc BRec) : Prop :=
  ∀ bl B, bs !! bl = some B → bktPg W B

theorem txPg_insert (W : WView) (bs : GMap Loc BRec) (bl : Loc) (B : BRec) (h : txPg W bs)
    (hB : bktPg W B) : txPg W (<[bl := B]> bs) := by
  intro y C hy
  by_cases hyl : y = bl
  · subst hyl; rw [GMap.lookup_insert] at hy; cases hy; exact hB
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hyl)] at hy; exact h y C hy

end pure

end bbolt
end EtcdGrove
end Perennial
