/-
A page position materialized during rebalance (`b.node` of a sibling, or of the root's only
child, `nodeAdded` of `Model/WOps`): the bucket stays in the rebalance's invariant, the new node's
bounds its entry's (`rbl_nodeAdded`), and the nested buckets' entries stay. Ported from
`old/bbolt/.../RebalanceMat.lean` and the parts of `old/bbolt/.../{WriteTxClean,ShapeMat}.lean`
it used (`bktClean_addChild`, `keys_addChild`, `entryIn_addChild`), over the new model (the tokens
are gone).

During rebalance `wOK` does not hold, so `wOK_nodeAdded` does not apply: the bucket's
cleanliness is proved here from `rblB` (`mat_clean`). `nodeAdded` does not determine all of the
new node's record: its `ins`, its `key'` slice and its bucket entries' value sources, and the
parent's `capOwn`, are premises here (`matExtra`, `matParent`; see `rbl_nodeAdded`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblCol
public import Proof.go_etcd_io.bbolt.Model.WOps
public import Proof.go_etcd_io.bbolt.Read.TreeFacts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pages
variable [GooseExts]

theorem mat_W64_toNat (x : w64) : W64 (x.toNat : Int) = x := by
  simp only [W64, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem mat_W64_eq_iff (d : Nat) (c : w64) (hd : d < 2 ^ 64) : W64 (d : Int) = c ↔ d = c.toNat := by
  constructor
  · intro h; rw [← h, toNat_W64_of_lt d hd]
  · intro h; rw [h, mat_W64_toNat]

theorem mat_pageWs_length (pg : List w8) : (pageWs pg).length = pageCount pg := by
  simp [pageWs]

theorem mat_pageWs_get (pg : List w8) (j : Nat) :
    (pageWs pg)[j]? = if j < pageCount pg then some (pageW pg j) else none := by
  unfold pageWs
  rw [List.getElem?_map]
  split
  · rw [List.getElem?_range ‹_›]; rfl
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem mat_pageW_leaf (pg : List w8) (j : Nat) (hl : pageFlags pg = leafPageFlag) :
    (pageW pg j).flags = W32 (leafFlags pg j : Int) ∧ (pageW pg j).pgid = W64 0 ∧
      (pageW pg j).key = leafKey pg j ∧ (pageW pg j).value = leafValue pg j := by
  unfold pageW; rw [if_pos hl]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem mat_pageW_branch (pg : List w8) (j : Nat) (hl : pageFlags pg ≠ leafPageFlag) :
    (pageW pg j).pgid = W64 (branchPgid pg j : Int) ∧ (pageW pg j).key = branchKey pg j := by
  unfold pageW; rw [if_neg hl]; exact ⟨rfl, rfl⟩

theorem mat_pageW_key (pg : List w8) (j : Nat) : (pageW pg j).key = pageKey pg j := by
  unfold pageW pageKey
  by_cases h : pageFlags pg = leafPageFlag
  · rw [if_pos h, if_pos (by rw [h]; rfl)]
  · rw [if_neg h, if_neg (by intro h'; exact h (by rw [h']; rfl))]

theorem mat_branch_ne_leaf : branchPageFlag ≠ leafPageFlag := by
  unfold branchPageFlag leafPageFlag; decide

theorem mat_wDat_eq {x y : WEntry} (h : wDat x = wDat y) :
    x.flags = y.flags ∧ x.pgid = y.pgid ∧ x.key = y.key ∧ x.value = y.value := by
  simpa [wDat] using h

theorem mat_pageWsAs_wDat (pg : List w8) (src : Src) :
    (pageWsAs pg src).map wDat = (pageWs pg).map wDat := by
  unfold pageWsAs; simp only [List.map_map]; rfl

/-- Entries equal to a page's by data: entry `j` is the page's. -/
theorem mat_at {ws : List WEntry} {pg : List w8} (hd : ws.map wDat = (pageWs pg).map wDat)
    (j : Nat) (x : WEntry) (hx : ws[j]? = some x) :
    j < pageCount pg ∧ wDat x = wDat (pageW pg j) := by
  have h := congrArg (fun l => l[j]?) hd
  simp only [List.getElem?_map, hx, mat_pageWs_get] at h
  by_cases hj : j < pageCount pg
  · simp only [hj, if_true, Option.map_some] at h
    exact ⟨hj, Option.some.inj h⟩
  · simp [hj] at h

theorem mat_at' {ws : List WEntry} {pg : List w8} (hd : ws.map wDat = (pageWs pg).map wDat)
    (j : Nat) (hj : j < pageCount pg) : ∃ x, ws[j]? = some x ∧ wDat x = wDat (pageW pg j) := by
  have h := congrArg (fun l => l[j]?) hd
  simp only [List.getElem?_map, mat_pageWs_get, hj, if_true, Option.map_some] at h
  cases hx : ws[j]? with
  | none => rw [hx] at h; cases h
  | some x => rw [hx] at h; exact ⟨x, rfl, Option.some.inj h⟩

theorem mat_len {ws : List WEntry} {pg : List w8} (hd : ws.map wDat = (pageWs pg).map wDat) :
    ws.length = pageCount pg := by
  have := congrArg List.length hd
  simpa [mat_pageWs_length] using this

theorem mat_keys {ws : List WEntry} {pg : List w8} (hd : ws.map wDat = (pageWs pg).map wDat) :
    ws.map WEntry.key = (pageWs pg).map WEntry.key := by
  have := congrArg (List.map (fun d : w32 × w64 × List w8 × List w8 => d.2.2.1)) hd
  simpa [List.map_map, Function.comp_def, wDat] using this

theorem mat_pgids {ws : List WEntry} {pg : List w8} (hd : ws.map wDat = (pageWs pg).map wDat) :
    ws.map WEntry.pgid = (pageWs pg).map WEntry.pgid := by
  have := congrArg (List.map (fun d : w32 × w64 × List w8 × List w8 => d.2.1)) hd
  simpa [List.map_map, Function.comp_def, wDat] using this

theorem mat_wKey_eq (ws : List WEntry) (j : Nat) :
    wKey ws j = ((ws.map WEntry.key)[j]?).getD [] := by
  unfold wKey; rw [List.getElem?_map]

theorem mat_wKey {ws : List WEntry} {pg : List w8} (hd : ws.map wDat = (pageWs pg).map wDat)
    (j : Nat) : wKey ws j = wKey (pageWs pg) j := by
  rw [mat_wKey_eq, mat_wKey_eq, mat_keys hd]

theorem mat_wKey_page (pg : List w8) (j : Nat) (hj : j < pageCount pg) :
    wKey (pageWs pg) j = pageKey pg j := by
  unfold wKey; rw [mat_pageWs_get, if_pos hj]; simp [mat_pageW_key]

theorem mat_wEntryBnd {ws : List WEntry} {pg : List w8} (hd : ws.map wDat = (pageWs pg).map wDat)
    (b : Option (List w8) × Option (List w8)) (j : Nat) :
    wEntryBnd b ws j = wEntryBnd b (pageWs pg) j := by
  unfold wEntryBnd; rw [mat_keys hd]

theorem mat_getD_key (pg : List w8) (j : Nat) (hj : j < pageCount pg)
    (hl : pageFlags pg ≠ leafPageFlag) :
    ((pageWs pg).map WEntry.key).getD j [] = branchKey pg j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, mat_pageWs_get, if_pos hj]
  simp [(mat_pageW_branch pg j hl).2]

/-- The bounds of a child of a node read from a branch page: its page's. -/
theorem mat_entryBnd_page (b : Option (List w8) × Option (List w8)) (pg : List w8) (i : Nat)
    (hi : i < pageCount pg) (hl : pageFlags pg ≠ leafPageFlag) :
    wEntryBnd b (pageWs pg) i =
      (childLo b.1 (branchKey pg) i, childHi b.2 (branchKey pg) (pageCount pg) i) := by
  unfold wEntryBnd entryBnd childLo childHi
  rw [List.length_map, mat_pageWs_length]
  congr 1
  · split
    · rfl
    · exact congrArg some (mat_getD_key pg i hi hl)
  · split
    · rename_i h; exact congrArg some (mat_getD_key pg (i + 1) h hl)
    · rfl

/-- The keys of a page are inside the bounds of its tree. -/
theorem mat_treeKeys_key (pages : Pages) (c : Nat) (lo hi : Option (List w8)) (pg : List w8)
    (h : treeKeys pages c lo hi) (hpg : pages !! c = some pg) :
    ∀ j < pageCount pg, keyIn lo hi (pageKey pg j) := by
  intro j hj
  cases h with
  | leaf _ pg' _ _ hpg' hl hk _ =>
    rw [hpg] at hpg'; cases hpg'
    unfold pageKey; rw [if_pos (by rw [hl]; rfl)]; exact hk j hj
  | branch _ pg' _ _ _ hpg' hb _ hk _ _ =>
    rw [hpg] at hpg'; cases hpg'
    unfold pageKey; rw [if_neg (by rw [hb]; unfold branchPageFlag; decide)]; exact hk j hj

theorem mat_isBktFlag_iff (x : Nat) (h : x < 2 ^ 32) :
    isBktFlag (W32 (x : Int)) ↔ x % 2 = bucketLeafFlag := by
  unfold isBktFlag bucketLeafFlag
  have h2 : (W32 (x : Int)).toNat = x := by
    rw [BitVec.toNat_ofInt]; simp; omega
  have hk : (W32 (x : Int) &&& W32 1).toNat = x % 2 := by
    rw [BitVec.toNat_and, h2]
    show x &&& 1 = x % 2
    rw [Nat.and_one_is_mod]
  constructor
  · intro hb
    refine Classical.byContradiction fun hc => hb ?_
    apply BitVec.eq_of_toNat_eq
    rw [hk]; simp; omega
  · intro hb he
    have := congrArg BitVec.toNat he
    rw [hk] at this; simp at this; omega

theorem mat_leafFlags_lt (pg : List w8) (i : Nat) : leafFlags pg i < 2 ^ 32 := by
  unfold leafFlags; exact BitVec.isLt _

theorem mat_branchPgid_lt (pg : List w8) (i : Nat) : branchPgid pg i < 2 ^ 64 := by
  unfold branchPgid; exact BitVec.isLt _

theorem mat_bytesAt_length (pg : List w8) (off n : Nat) (h : off + n ≤ pg.length) :
    (bytesAt pg off n).length = n := by
  unfold bytesAt; simp; omega

/-- A page tree's page: a leaf or a branch, with its facts. -/
theorem mat_kind {P : Pages} {hwm : Nat} {pg : List w8} {len : Nat}
    (hpt : pageTreeWF P hwm pg len) :
    (pageFlags pg = leafPageFlag ∧ leafWF pg len ∧ ∀ i < pageCount pg,
      leafFlags pg i % 2 = bucketLeafFlag → bucketWF P hwm (leafValue pg i)) ∨
    (pageFlags pg = branchPageFlag ∧ branchWF pg len hwm ∧ ∀ i < pageCount pg,
      treeWF P hwm (branchPgid pg i)) := by
  cases hpt with
  | leaf _ _ a b c => exact Or.inl ⟨a, b, c⟩
  | branch _ _ a b c => exact Or.inr ⟨a, b, c⟩

theorem mat_ptwf {P : Pages} {hwm c : Nat} {pg : List w8} (h : treeWF P hwm c)
    (hpg : P !! c = some pg) : pageId pg = c ∧ c < hwm ∧ pageTreeWF P hwm pg pg.length := by
  cases h with
  | page _ pg' _ hlt hpg' hid _ hpt => rw [hpg] at hpg'; cases hpg'; exact ⟨hid, hlt, hpt⟩

theorem mat_has_lt {P : Pages} {hwm c d : Nat} (h : treeWF P hwm c) (hd : treeHas P c d) :
    d < 2 ^ 64 := by
  have hw := Read.treeHas_treeWF P hwm hd h
  cases hw with
  | page _ pg _ _ _ hid _ _ => rw [← hid]; unfold pageId; exact BitVec.isLt _

theorem mat_treeHas_child {P : Pages} {c : Nat} {pg : List w8} (hpg : P !! c = some pg)
    (hb : pageFlags pg = branchPageFlag) (j : Nat) (hj : j < pageCount pg) (d : Nat)
    (h : treeHas P (branchPgid pg j) d) : treeHas P c d :=
  treeHas.sub _ pg d hpg (pageHas.child pg j d hb hj h)

theorem mat_strict (v : View) (hv : viewWF v) : pagesStrict v.pages := by
  obtain ⟨C, hok, hvC⟩ := hv
  rw [← hvC]; exact hok.1.2.1

theorem mat_nodup_map_on {α β : Type} (f : α → β) : ∀ (l : List α), l.Nodup →
    (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; exact List.nodup_nil
  | cons x xs ih =>
    intro hn h
    obtain ⟨hx, hxs⟩ := List.nodup_cons.1 hn
    refine List.nodup_cons.2 ⟨?_, ih hxs fun a ha b hb =>
      h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩
    intro hm
    obtain ⟨y, hy, hfy⟩ := List.mem_map.1 hm
    exact hx (h y (List.mem_cons_of_mem _ hy) x List.mem_cons_self hfy ▸ hy)

end pages

section mat
variable [GooseExts]

theorem mat_pageKey_leaf (pg : List w8) (j : Nat) (hf : pageFlags pg = leafPageFlag) :
    pageKey pg j = leafKey pg j := by
  unfold pageKey; rw [if_pos (by rw [hf]; rfl)]

theorem mat_pageKey_branch (pg : List w8) (j : Nat) (hf : pageFlags pg = branchPageFlag) :
    pageKey pg j = branchKey pg j := by
  unfold pageKey; rw [if_neg (by rw [hf]; unfold branchPageFlag; decide)]

/-! ### The materialized bucket -/

/-- The new node `r` read from the page `pg` under `nl`, as `nodeAdded` gives it. -/
def matNew (bl nl : Loc) (pg : List w8) (r : NRec) : Prop :=
  r.nv.bucket' = bl ∧ r.nv.parent' = nl ∧ r.nv.pgid' = (pageHdr pg).id' ∧
  r.nv.isLeaf' = decide (pageFlags pg = leafPageFlag) ∧ r.nv.unbalanced' = false ∧
  r.nv.spilled' = false ∧ r.cs = [] ∧ r.capOwn = true ∧ r.ws.map wDat = (pageWs pg).map wDat ∧
  wsLive r.ws ∧ r.key = wKey r.ws 0 ∧ r.ksrc ≠ Src.stale

/-- What `nodeAdded` does not say of the new node and `node.read` makes true: one inode per
entry, a non-nil key slice, nested buckets' values persistent or in the view. -/
def matExtra (r : NRec) : Prop :=
  r.ins.length = r.ws.length ∧ r.nv.key' ≠ slice.nil ∧
  ∀ w ∈ r.ws, isBktFlag w.flags → w.vs = Src.view ∨ w.vs = Src.own DFrac.discard

/-- The parent `rp'` after `rp` got the child `l`, as `nodeAdded` gives it, and its `capOwn`
kept (which `nodeAdded` does not say). -/
def matParent (rp rp' : NRec) (l : Loc) : Prop :=
  rp'.cs = rp.cs ++ [l] ∧ rp'.ws = rp.ws ∧ rp'.ins = rp.ins ∧ rp'.key = rp.key ∧
  rp'.ksrc = rp.ksrc ∧ rp'.nv = { rp.nv with children' := rp'.nv.children' } ∧
  rp'.capOwn = rp.capOwn

/-- The bucket after the page `c` was materialized as the node `l` (record `r`) under `nl`
(record `rp'`). -/
def matBkt (B : BRec) (c : w64) (nl l : Loc) (rp' r : NRec) : BRec :=
  { B with nm := B.nm.insert c l, ns := (B.ns.insert nl rp').insert l r }

theorem mat_ns (B : BRec) (c : w64) (nl l : Loc) (rp' r : NRec) (y : Loc) :
    (matBkt B c nl l rp' r).ns !! y =
      if y = l then some r else if y = nl then some rp' else B.ns !! y := by
  show ((B.ns.insert nl rp').insert l r) !! y = _
  by_cases h1 : y = l
  · subst h1; rw [GMap.lookup_insert, if_pos rfl]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h1), if_neg h1]
    by_cases h2 : y = nl
    · subst h2; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h2), if_neg h2]

theorem mat_nm (B : BRec) (c : w64) (nl l : Loc) (rp' r : NRec) (k : w64) :
    (matBkt B c nl l rp' r).nm !! k = if k = c then some l else B.nm !! k := by
  show (B.nm.insert c l) !! k = _
  by_cases hk : k = c
  · subst hk; rw [GMap.lookup_insert, if_pos rfl]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk), if_neg hk]

/-- A node's well-formedness survives the bucket's growing by a node for the page `c`, which is
none of its children nor itself. -/
theorem mat_nodeClean_frame (W : View) (hwm : Nat) (bl : Loc) (B B' : BRec) (x : Loc) (r : NRec)
    (c : w64) (hib : B'.ib = B.ib) (hbm : B'.bm = B.bm) (hrn : B'.bv.rootNode' = B.bv.rootNode')
    (hnm : ∀ k, k ≠ c → B'.nm !! k = B.nm !! k)
    (hns : ∀ y ry, B.ns !! y = some ry → ∃ ry', B'.ns !! y = some ry' ∧
      ry'.nv.parent' = ry.nv.parent' ∧ ry'.nv.isLeaf' = ry.nv.isLeaf' ∧ ry'.ws = ry.ws ∧
      ∀ z ∈ ry.cs, z ∈ ry'.cs)
    (hx : r.nv.isLeaf' = false → ∀ w ∈ r.ws, w.pgid ≠ c) (hpgid : r.nv.pgid' ≠ c)
    (h : nodeClean W hwm bl B x r) : nodeClean W hwm bl B' x r := by
  obtain ⟨h1, h0, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  refine ⟨h1, h0, h2, h3, h4, h5, h6, by rw [hnm _ hpgid]; exact h7, by rw [hib]; exact h8,
    by rw [hib]; exact h9, h10, by rw [hbm]; exact h11, ?_, by rw [hrn]; exact h13, ?_, h15, ?_⟩
  · intro hl
    obtain ⟨a, b, hk⟩ := h12 hl
    refine ⟨a, b, fun w hw => ?_⟩
    obtain ⟨k1, k2, k3⟩ := hk w hw
    have hne := hx hl w hw
    refine ⟨k1, fun l' hl' => ?_, fun hn => k3 (by rw [← hnm _ hne]; exact hn)⟩
    rw [hnm _ hne] at hl'
    obtain ⟨r', hr', hp⟩ := k2 l' hl'
    obtain ⟨ry', hy', hp', -⟩ := hns l' r' hr'
    exact ⟨ry', hy', hp'.trans hp⟩
  · intro hp
    obtain ⟨rp, hrp, hleaf, hmem, w, hw, hwp⟩ := h14 hp
    obtain ⟨rp', hrp', -, hleaf', hws, hcs⟩ := hns _ rp hrp
    exact ⟨rp', hrp', hleaf'.trans hleaf, hcs x hmem, w, hws ▸ hw, hwp⟩
  · intro z hz
    obtain ⟨rc, hrc, hpc⟩ := h16 z hz
    obtain ⟨rc', hrc', hpc', -⟩ := hns z rc hrc
    exact ⟨rc', hrc', hpc'.trans hpc⟩

section child
variable (W : View) (hwm : Nat) (bl : Loc) (B : BRec) (hv : pagesStrict W.pages)
    (hc : bktClean W hwm bl B) (nl : Loc) (rp : NRec) (i : Nat) (w : WEntry)
    (hrp : B.ns !! nl = some rp) (hbr : rp.nv.isLeaf' = false) (hw : rp.ws[i]? = some w)
    (hnone : B.nm !! w.pgid = none) (l : Loc) (hfresh : B.ns !! l = none) (hl : l ≠ null)
    (pg : List w8) (hpg : W.pages !! w.pgid.toNat = some pg) (r rp' : NRec)
    (hr : matNew bl nl pg r) (hp' : matParent rp rp' l)
include hv hc hrp hbr hw hnone hfresh hl hpg hr hp'

set_option linter.unusedVariables false in
theorem mat_basic :
    B.ib.root' ≠ W64 0 ∧ B.bv.rootNode' ≠ null ∧ nl ≠ null ∧ l ≠ nl ∧ rp.nv.pgid' ≠ w.pgid ∧
      (pageHdr pg).id' = w.pgid ∧ treeWF W.pages hwm w.pgid.toNat ∧
      pageTreeWF W.pages hwm pg pg.length ∧ pagePosAt B nl i w.pgid := by
  have hroot : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc.2.2.2.2.2.2.1 h0 nl rp hrp; rw [hbr] at this; cases this
  have hrn : B.bv.rootNode' ≠ null := by
    intro h0; have := (hc.2.2.1 h0).1; rw [this] at hrp; cases hrp
  have hNrp := hc.2.2.2.2.2.2.2.1 nl rp hrp
  have hrp8 := ncol_nm hNrp
  have hnl : nl ≠ null := (hc.2.2.2.2.1 _ _ hrp8).1
  have hlnl : l ≠ nl := by intro h; rw [h, hrp] at hfresh; cases hfresh
  have hpgc : rp.nv.pgid' ≠ w.pgid := by intro h; rw [h, hnone] at hrp8; cases hrp8
  have hwfc := ((ncol_br hNrp hbr).2.2 w (List.mem_of_getElem? hw)).2.2 hnone
  obtain ⟨hid, -, hpt⟩ := mat_ptwf hwfc hpg
  exact ⟨hroot, hrn, hnl, hlnl, hpgc, BitVec.eq_of_toNat_eq hid, hwfc, hpt,
    ⟨rp, w, hrp, hbr, hw, rfl, hnone⟩⟩

/-- The old nodes' records in the grown bucket. -/
theorem mat_nsB : ∀ y ry, B.ns !! y = some ry → ∃ ry', (matBkt B w.pgid nl l rp' r).ns !! y = some ry' ∧
      ry'.nv.parent' = ry.nv.parent' ∧ ry'.nv.isLeaf' = ry.nv.isLeaf' ∧ ry'.ws = ry.ws ∧
      ry'.nv.pgid' = ry.nv.pgid' ∧ (∀ z ∈ ry.cs, z ∈ ry'.cs) ∧ ry'.nv.key' = ry.nv.key' ∧
      ry'.key = ry.key ∧ ry'.nv.unbalanced' = ry.nv.unbalanced' := by
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hp'
  intro y ry hy
  have hyl : y ≠ l := by intro h; rw [h, hfresh] at hy; cases hy
  rw [mat_ns, if_neg hyl]
  by_cases hyn : y = nl
  · rw [if_pos hyn]; rw [hyn, hrp] at hy; cases hy
    refine ⟨rp', rfl, (show rp'.nv.parent' = rp.nv.parent' by rw [hp6]), (show rp'.nv.isLeaf' = rp.nv.isLeaf' by rw [hp6]), hp2,
      (show rp'.nv.pgid' = rp.nv.pgid' by rw [hp6]), fun z hz => ?_, (show rp'.nv.key' = rp.nv.key' by rw [hp6]), hp4,
      (show rp'.nv.unbalanced' = rp.nv.unbalanced' by rw [hp6])⟩
    rw [hp1]; exact List.mem_append_left _ hz
  · rw [if_neg hyn]; exact ⟨ry, hy, rfl, rfl, rfl, rfl, fun z hz => hz, rfl, rfl, rfl⟩

/-- The page positions of the grown bucket: the new node's children, or old ones but the
materialized one. -/
theorem mat_pos : ∀ x j c', pagePosAt (matBkt B w.pgid nl l rp' r) x j c' →
      (x = l ∧ pageFlags pg = branchPageFlag ∧ j < pageCount pg ∧
        c' = W64 (branchPgid pg j : Int)) ∨ (pagePosAt B x j c' ∧ (x, j) ≠ (nl, i)) := by
  obtain ⟨-, -, -, -, -, -, -, hpt, -⟩ :=
    mat_basic W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12⟩ := hr
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hp'
  have hkind := mat_kind hpt
  intro x j c' ⟨ry, wy, hy, hyleaf, hwy, hwyp, hnmy⟩
  rw [mat_nm] at hnmy
  split at hnmy
  · cases hnmy
  rename_i hc'
  rw [mat_ns] at hy
  by_cases hxl : x = l
  · rw [if_pos hxl] at hy; cases hy
    left
    have hnleaf : pageFlags pg ≠ leafPageFlag := by
      intro h; rw [hr4, h] at hyleaf; simp at hyleaf
    have hbr' : pageFlags pg = branchPageFlag := by
      rcases hkind with ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hnleaf
      · exact h
    obtain ⟨hj, hd⟩ := mat_at hr9 j wy hwy
    refine ⟨hxl, hbr', hj, ?_⟩
    rw [← hwyp, (mat_wDat_eq hd).2.1, (mat_pageW_branch pg j hnleaf).1]
  · rw [if_neg hxl] at hy
    right
    by_cases hxn : x = nl
    · rw [if_pos hxn] at hy; cases hy
      rw [hp2] at hwy
      refine ⟨⟨rp, wy, by rw [hxn]; exact hrp, hbr, hwy, hwyp, hnmy⟩, ?_⟩
      intro he
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      rw [hw] at hwy; cases hwy
      exact hc' hwyp.symm
    · rw [if_neg hxn] at hy
      refine ⟨⟨ry, wy, hy, hyleaf, hwy, hwyp, hnmy⟩, ?_⟩
      intro he; simp only [Prod.mk.injEq] at he; exact hxn he.1

/-- Materializing the page position `w.pgid` (entry `i` of the branch node `nl`, a page with
entries) keeps a bucket clean. -/
theorem mat_clean (hx : matExtra r) (hcnt : 0 < pageCount pg) :
    bktClean W hwm bl (matBkt B w.pgid nl l rp' r) := by
  obtain ⟨hroot, hrn, hnl, hlnl, hpgc, hcid, hwfc, hpt, hpos⟩ :=
    mat_basic W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hnsB := mat_nsB W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hposB' := mat_pos W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12⟩ := hr
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hp'
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩ := hc
  have hNrp := hc8 nl rp hrp
  have hgood := hv.1 _ pg hpg
  have huniq := hv.2
  have hcself : treeHas W.pages w.pgid.toNat w.pgid.toNat := treeHas.root _ pg hpg
  have hkind := mat_kind hpt
  have hwmem : w ∈ rp.ws := List.mem_of_getElem? hw
  have hnm' := mat_nm B w.pgid nl l rp' r
  have hns' := mat_ns B w.pgid nl l rp' r
  have hpl : rp'.nv.isLeaf' = rp.nv.isLeaf' := (show rp'.nv.isLeaf' = rp.nv.isLeaf' by rw [hp6])
  have hpp : rp'.nv.parent' = rp.nv.parent' := (show rp'.nv.parent' = rp.nv.parent' by rw [hp6])
  have hppg : rp'.nv.pgid' = rp.nv.pgid' := (show rp'.nv.pgid' = rp.nv.pgid' by rw [hp6])
  have hsub : ∀ j, j < pageCount pg → pageFlags pg = branchPageFlag → ∀ d,
      treeHas W.pages (W64 (branchPgid pg j : Int)).toNat d → treeHas W.pages w.pgid.toNat d := by
    intro j hj hb d hd
    rw [toNat_W64_of_lt _ (mat_branchPgid_lt pg j)] at hd
    exact mat_treeHas_child hpg hb j hj d hd
  have hnotc : ∀ j, j < pageCount pg → pageFlags pg = branchPageFlag →
      ¬ treeHas W.pages (W64 (branchPgid pg j : Int)).toNat w.pgid.toNat := by
    intro j hj hb hd
    rw [toNat_W64_of_lt _ (mat_branchPgid_lt pg j)] at hd
    exact (huniq.1 _ pg hpg hb).2 j hj hd
  have hposwf : ∀ x j c', pagePosAt B x j c' → treeWF W.pages hwm c'.toNat := by
    rintro x j c' ⟨ry, wy, hy, hyl, hwy, rfl, hn⟩
    exact ((ncol_br (hc8 x ry hy) hyl).2.2 wy (List.mem_of_getElem? hwy)).2.2 hn
  have hnodes : ∀ j, j < pageCount pg → 0 < (pageKey pg j).length := by
    intro j hj
    rcases hkind with ⟨hf, hwf, -⟩ | ⟨hf, hwf, -⟩
    · have hk := (hgood.1 hf j hj).1
      have hb := (hwf.2.2.1 j hj).1
      rw [mat_pageKey_leaf pg j hf]; unfold leafKey
      rw [mat_bytesAt_length _ _ _ (by omega)]; exact hk
    · have hk := hgood.2 hf j hj
      have hb := (hwf.2.2.2.1 j hj).1
      rw [mat_pageKey_branch pg j hf]; unfold branchKey
      rw [mat_bytesAt_length _ _ _ (by omega)]; exact hk
  refine ⟨fun h => absurd h hroot, hc2, fun h => absurd h hrn, fun h => ?_, ?_, hc6,
    fun h => absurd h hroot, ?_, ?_, ?_⟩
  · have h4 := hc4 h
    have hne : B.ib.root' ≠ w.pgid := by intro he; rw [he, hnone] at h4; cases h4
    show (matBkt B w.pgid nl l rp' r).nm !! B.ib.root' = some B.bv.rootNode'
    rw [hnm', if_neg hne]; exact h4
  · intro k l' hk
    rw [hnm'] at hk
    split at hk
    · rename_i hkc; cases hk
      refine ⟨hl, r, by rw [hns', if_pos rfl], ?_⟩
      rw [hkc, hr3]; exact hcid
    · obtain ⟨hl', r', hr', hp''⟩ := hc5 k l' hk
      obtain ⟨ry', hy', -, -, -, hpg', -⟩ := hnsB l' r' hr'
      exact ⟨hl', ry', hy', hpg'.trans hp''⟩
  · -- every node
    intro y ry hy
    rw [hns'] at hy
    by_cases hyl : y = l
    · -- the new node
      rw [if_pos hyl] at hy; cases hy
      have hsorted : wsSorted r.ws := by
        intro a b hab hb
        rw [mat_len hr9] at hb
        rw [mat_wKey hr9, mat_wKey hr9, mat_wKey_page pg a (by omega), mat_wKey_page pg b hb]
        rcases hkind with ⟨hf, hwf, -⟩ | ⟨hf, hwf, -⟩
        · rw [mat_pageKey_leaf pg a hf, mat_pageKey_leaf pg b hf]
          exact hwf.2.2.2 a b hab hb
        · rw [mat_pageKey_branch pg a hf, mat_pageKey_branch pg b hf]
          exact hwf.2.2.2.2 a b hab hb
      have hkeys : ∀ x ∈ r.ws, 0 < x.key.length := by
        intro x hx
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
        obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
        rw [(mat_wDat_eq hd).2.2.1, mat_pageW_key]; exact hnodes j hjc
      refine ⟨hr1, hr8, hx1, hsorted, hkeys, hr10, hr6, ?_, fun h => absurd h hroot, fun _ => ?_,
        Or.inr ⟨?_, hr12⟩, ?_, ?_, fun h => absurd (hr2.symm.trans h) hnl, fun _ => ?_,
        by rw [hr7]; exact List.nodup_nil, fun z hz => by rw [hr7] at hz; cases hz⟩
      · show (matBkt B w.pgid nl l rp' r).nm !! r.nv.pgid' = some y
        rw [hr3, hcid, hnm', if_pos rfl, hyl]
      · rw [hr3, hcid]; exact hwfc
      · rw [hr11, mat_wKey hr9, mat_wKey_page pg 0 hcnt]; exact hnodes 0 hcnt
      · intro hleaf x hx hbk
        have hfl : pageFlags pg = leafPageFlag := by rw [hr4] at hleaf; simpa using hleaf
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
        obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
        obtain ⟨e1, -, -, e4⟩ := mat_wDat_eq hd
        obtain ⟨f1, -, -, f4⟩ := mat_pageW_leaf pg j hfl
        have hbk' : leafFlags pg j % 2 = bucketLeafFlag := by
          rw [e1, f1, mat_isBktFlag_iff _ (mat_leafFlags_lt pg j)] at hbk; exact hbk
        rcases hkind with ⟨-, -, hbw⟩ | ⟨hb, -, -⟩
        · refine ⟨fun _ => ?_, hx3 x hx hbk⟩
          rw [e4, f4]
          exact ⟨hbw j hjc hbk', fun h0 => (hgood.1 hfl j hjc).2 hbk' h0⟩
        · rw [hb] at hfl; exact absurd hfl mat_branch_ne_leaf
      · intro hleaf
        have hnleaf : pageFlags pg ≠ leafPageFlag := by
          intro h; rw [hr4, h] at hleaf; simp at hleaf
        rcases hkind with ⟨h, -⟩ | ⟨hb, hbw, hbk⟩
        · exact absurd h hnleaf
        refine ⟨by rw [mat_len hr9]; exact hbw.1, ?_, ?_⟩
        · rw [mat_pgids hr9]
          have hmap : (pageWs pg).map WEntry.pgid =
              (List.range (pageCount pg)).map fun j => W64 (branchPgid pg j : Int) := by
            unfold pageWs; rw [List.map_map]; congr 1; funext j
            exact (mat_pageW_branch pg j hnleaf).1
          rw [hmap]
          refine mat_nodup_map_on _ _ List.nodup_range ?_
          intro a ha b hb' hab
          have ha' := List.mem_range.1 ha
          have hb'' := List.mem_range.1 hb'
          refine Classical.byContradiction fun hne => ?_
          have hax : branchPgid pg a = branchPgid pg b := by
            have := congrArg BitVec.toNat hab
            rwa [toNat_W64_of_lt _ (mat_branchPgid_lt _ _),
              toNat_W64_of_lt _ (mat_branchPgid_lt _ _)] at this
          cases hbk a ha' with
          | page _ pga _ _ hpga _ _ _ =>
            exact (huniq.1 _ pg hpg hb).1 a b ha' hb'' hne _ (treeHas.root _ pga hpga)
              (hax ▸ treeHas.root _ pga hpga)
        · intro x hx
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
          obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
          have hpj : x.pgid = W64 (branchPgid pg j : Int) := by
            rw [(mat_wDat_eq hd).2.1, (mat_pageW_branch pg j hnleaf).1]
          rw [hpj]
          have hjne : W64 (branchPgid pg j : Int) ≠ w.pgid := by
            intro he
            apply hnotc j hjc hb
            rw [he]; exact hcself
          have hjnone : B.nm !! W64 (branchPgid pg j : Int) = none := by
            cases hbk j hjc with
            | page _ pgj _ _ hpgj _ _ _ =>
              exact hc10 nl i w.pgid hpos (branchPgid pg j)
                (mat_treeHas_child hpg hb j hjc _ (treeHas.root _ pgj hpgj))
          refine ⟨by rw [toNat_W64_of_lt _ (mat_branchPgid_lt _ _)]; exact (hbw.2.2.2.1 j hjc).2.2,
            ?_, ?_⟩
          · intro l' hl'; rw [hnm', if_neg hjne, hjnone] at hl'; cases hl'
          · intro _; rw [toNat_W64_of_lt _ (mat_branchPgid_lt _ _)]; exact hbk j hjc
      · rw [hr2]
        refine ⟨rp', by rw [hns', if_neg (Ne.symm hlnl), if_pos rfl], by rw [hpl]; exact hbr, ?_, w,
          by rw [hp2]; exact hwmem, by rw [hr3, hcid]⟩
        rw [hp1, hyl]; exact List.mem_append_right _ (List.mem_singleton_self _)
    · rw [if_neg hyl] at hy
      by_cases hyn : y = nl
      · -- the parent
        rw [if_pos hyn] at hy; cases hy
        obtain ⟨h1, h0, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hNrp
        rw [hyn]
        refine ⟨by rw [(show rp'.nv.bucket' = rp.nv.bucket' by rw [hp6])]; exact h1, by rw [hp7]; exact h0,
          by rw [hp3, hp2]; exact h2, by rw [hp2]; exact h3, by rw [hp2]; exact h4,
          by rw [hp2]; exact h5, by rw [(show rp'.nv.spilled' = rp.nv.spilled' by rw [hp6])]; exact h6, ?_,
          by rw [hppg]; exact h8, by rw [hppg]; exact h9,
          by rw [(show rp'.nv.key' = rp.nv.key' by rw [hp6]), hp4, hp5]; exact h10, by rw [hpl, hp2]; exact h11, ?_,
          by rw [hpp]; exact h13, ?_, ?_, ?_⟩
        · show (matBkt B w.pgid nl l rp' r).nm !! rp'.nv.pgid' = some nl
          rw [hppg, hnm', if_neg hpgc]; exact h7
        · intro hb'
          rw [hpl] at hb'
          obtain ⟨a, b, hk⟩ := h12 hb'
          rw [hp2]
          refine ⟨a, b, fun w' hw' => ?_⟩
          obtain ⟨k1, k2, k3⟩ := hk w' hw'
          refine ⟨k1, fun l' hl' => ?_, fun hn => ?_⟩
          · rw [hnm'] at hl'
            split at hl'
            · cases hl'; exact ⟨r, by rw [hns', if_pos rfl], hr2⟩
            · obtain ⟨r', hr', hp''⟩ := k2 l' hl'
              obtain ⟨ry', hy', hpp', -⟩ := hnsB l' r' hr'
              exact ⟨ry', hy', hpp'.trans hp''⟩
          · rw [hnm'] at hn
            split at hn
            · cases hn
            · exact k3 hn
        · intro hp
          rw [hpp] at hp ⊢
          obtain ⟨g, hg, hgl, hgm, wg, hwg, hwgp⟩ := h14 hp
          obtain ⟨g', hg', -, hgl', hgws, -, hgcs, -⟩ := hnsB _ g hg
          exact ⟨g', hg', hgl'.trans hgl, hgcs nl hgm, wg, hgws ▸ hwg, by rw [hppg]; exact hwgp⟩
        · rw [hp1]
          refine List.nodup_append.2 ⟨h15, by simp, ?_⟩
          intro a ha b hb heq
          rw [List.mem_singleton] at hb
          rw [hb] at heq; rw [heq] at ha
          obtain ⟨rc, hrc, -⟩ := h16 _ ha
          rw [hfresh] at hrc; cases hrc
        · intro z hz
          rw [hp1] at hz
          rcases List.mem_append.1 hz with hz | hz
          · obtain ⟨rc, hrc, hpc⟩ := h16 z hz
            obtain ⟨rc', hrc', hpc', -⟩ := hnsB z rc hrc
            exact ⟨rc', hrc', hpc'.trans hpc⟩
          · rw [List.mem_singleton] at hz; rw [hz]
            exact ⟨r, by rw [hns', if_pos rfl], hr2⟩
      · -- another node
        rw [if_neg hyn] at hy
        refine mat_nodeClean_frame W hwm bl B (matBkt B w.pgid nl l rp' r) y ry w.pgid rfl rfl rfl
          (fun k hk => by rw [hnm', if_neg hk]) (fun y' ry' hy' => ?_) ?_ ?_ (hc8 y ry hy)
        · obtain ⟨a, b, c1, d, e, -, f, -⟩ := hnsB y' ry' hy'
          exact ⟨a, b, c1, d, e, f⟩
        · intro hb' w' hw' he
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hw'
          have hposy : pagePosAt B y j w.pgid := ⟨ry, w', hy, hb', hj, he, hnone⟩
          exact hc9 y j w.pgid nl i w.pgid hposy hpos
            (by intro h; simp only [Prod.mk.injEq] at h; exact hyn h.1) _ hcself hcself
        · intro he
          have h7 := ncol_nm (hc8 y ry hy)
          rw [he, hnone] at h7; cases h7
  · -- positions disjoint
    intro x1 j1 c1 x2 j2 c2 hP1 hP2 hne d hd1 hd2
    rcases hposB' x1 j1 c1 hP1 with ⟨rfl, hb, hj1, rfl⟩ | ⟨hq1, hn1⟩ <;>
      rcases hposB' x2 j2 c2 hP2 with ⟨rfl, hb2, hj2, rfl⟩ | ⟨hq2, hn2⟩
    · have hjne : j1 ≠ j2 := by intro h; exact hne (by rw [h])
      rw [toNat_W64_of_lt _ (mat_branchPgid_lt _ _)] at hd1
      rw [toNat_W64_of_lt _ (mat_branchPgid_lt _ _)] at hd2
      exact (huniq.1 _ pg hpg hb).1 j1 j2 hj1 hj2 hjne d hd1 hd2
    · exact hc9 nl i w.pgid x2 j2 c2 hpos hq2 (Ne.symm hn2) d (hsub j1 hj1 hb d hd1) hd2
    · exact hc9 x1 j1 c1 nl i w.pgid hq1 hpos hn1 d hd1 (hsub j2 hj2 hb2 d hd2)
    · exact hc9 x1 j1 c1 x2 j2 c2 hq1 hq2 hne d hd1 hd2
  · -- positions node-free
    intro x j c' hP d hd
    rw [hnm']
    split
    · rename_i hdc
      have hdlt : d < 2 ^ 64 := by
        rcases hposB' x j c' hP with ⟨-, hb, hj, rfl⟩ | ⟨hq, -⟩
        · exact mat_has_lt hwfc (hsub j hj hb d hd)
        · exact mat_has_lt (hposwf x j c' hq) hd
      rw [mat_W64_eq_iff _ _ hdlt] at hdc
      subst hdc
      rcases hposB' x j c' hP with ⟨-, hb, hj, rfl⟩ | ⟨hq, hn⟩
      · exact absurd hd (hnotc j hj hb)
      · exact absurd hcself (hc9 x j c' nl i w.pgid hq hpos hn _ hd)
    · rcases hposB' x j c' hP with ⟨-, hb, hj, rfl⟩ | ⟨hq, -⟩
      · exact hc10 nl i w.pgid hpos d (hsub j hj hb d hd)
      · exact hc10 x j c' hq d hd

end child

end mat

end bbolt
end EtcdGrove
end Perennial
