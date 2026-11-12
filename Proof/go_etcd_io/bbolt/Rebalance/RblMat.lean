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
public import Proof.go_etcd_io.bbolt.Write.Bound
public import Proof.go_etcd_io.bbolt.Write.BoundNest

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
theorem mat_clean (hx : matExtra r) (hcnt : 0 < pageCount pg) (hinl : Write.leafInl pg)
    (hnest : matNest W.pages pg) :
    bktClean W hwm bl (matBkt B w.pgid nl l rp' r) := by
  obtain ⟨hroot, hrn, hnl, hlnl, hpgc, hcid, hwfc, hpt, hpos⟩ :=
    mat_basic W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hnsB := mat_nsB W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hposB' := mat_pos W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12⟩ := hr
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hp'
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11⟩ := hc
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
          -- the nested-plainness clause, from the view page (`matNest`, `posShape`'s)
          exact ⟨hbw j hjc hbk', fun h0 => ⟨(hgood.1 hfl j hjc).2 hbk' h0, hinl hfl j hjc hbk' h0⟩,
            fun _ bpg hb => hnest hfl j hjc hbk' bpg hb⟩
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
  · -- positions node-free (and, batch 37, the cached children non-nil: `bm` unchanged)
    refine ⟨fun x j c' hP d hd => ?_, hc11⟩
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

/-- A node's keys during rebalance in a bucket that grew by a node (see the hypotheses). -/
theorem rblNodeKeys_frame (W : View) (B B' : BRec)
    (bnd bnd' : Loc → Option (List w8) × Option (List w8))
    (dfc : Option Loc) (y : Loc) (ry ry' : NRec) (h : rblNodeKeys W B bnd dfc y ry)
    (hb : bnd' y = bnd y)
    (hbp : ry.nv.parent' ≠ null → bnd' ry.nv.parent' = bnd ry.nv.parent')
    (hws : ry'.ws = ry.ws) (hpar : ry'.nv.parent' = ry.nv.parent')
    (hleaf : ry'.nv.isLeaf' = ry.nv.isLeaf')
    (hkey' : ry'.nv.key' = ry.nv.key') (hkey : ry'.key = ry.key) (hpgid : ry'.nv.pgid' = ry.nv.pgid')
    (hunb : ry'.nv.unbalanced' = ry.nv.unbalanced') (hbm : B'.bm = B.bm)
    (hns : ∀ z rz, B.ns !! z = some rz → ∃ rz', B'.ns !! z = some rz' ∧ rz'.ws = rz.ws ∧
      rz'.nv.isLeaf' = rz.nv.isLeaf')
    (hnmB : ∀ k l', B'.nm !! k = some l' → B.nm !! k = some l' ∨ (B.nm !! k = none ∧
      ∃ r', B'.ns !! l' = some r' ∧ ∀ pg, W.pages !! k.toNat = some pg →
        r'.nv.isLeaf' = decide (pageFlags pg = leafPageFlag)))
    (hnmN : ∀ k, B'.nm !! k = none → B.nm !! k = none) : rblNodeKeys W B' bnd' dfc y ry' := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := h
  refine ⟨by rw [hws, hb]; exact c1, ?_, ?_, by rw [hleaf, hunb, hpar, hws]; exact c4, by
      rw [hleaf, hws]; intro hl w hw
      refine ⟨(c5 hl w hw).1, fun hbk h0 hno => (c5 hl w hw).2 hbk h0 ?_⟩
      unfold opened at hno ⊢; rwa [hbm] at hno⟩
  · intro hp
    rw [hpar] at hp
    obtain ⟨hk', rp0, i0, w0, hrp0, hw0, hpg0, hkey0, hbnd0⟩ := c2 hp
    obtain ⟨rp0', h1, h2, -⟩ := hns _ _ hrp0
    refine ⟨by rw [hkey']; exact hk', rp0', i0, w0, by rw [hpar]; exact h1, by rw [h2]; exact hw0,
      by rw [hpgid]; exact hpg0, by rw [hkey]; exact hkey0, ?_⟩
    rw [hb, hpar, hbp hp, h2]; exact hbnd0
  · intro hlf
    rw [hleaf] at hlf
    obtain ⟨h2, hfst, kind, hkd⟩ := c3 hlf
    refine ⟨by rw [hws]; exact h2, by rw [hb, hws]; exact hfst, kind, fun j w' hj => ?_⟩
    rw [hws] at hj
    obtain ⟨ha, hbb⟩ := hkd j w' hj
    refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
    · rcases hnmB _ _ hl' with ho | ⟨hn0, r', hr', hlf'⟩
      · obtain ⟨r'', h1, h2⟩ := ha l' ho
        obtain ⟨r3, h3, -, h4⟩ := hns _ _ h1
        exact ⟨r3, h3, h4.trans h2⟩
      · obtain ⟨pg0, hpg0, -, hk0, -⟩ := hbb hn0
        exact ⟨r', hr', by rw [hlf' pg0 hpg0]; exact hk0⟩
    · obtain ⟨pg0, a1, a2, a3, a4, a5⟩ := hbb (hnmN _ hn)
      exact ⟨pg0, a1, a2, a3, a4, by rw [hb, hws]; exact a5⟩

theorem mat_ownHas_cases {pages : Pages} {c p : Nat} (pg : List w8)
    (hpg : pages !! c = some pg) (h : ownHas pages c p) :
    p = c ∨ (pageFlags pg = branchPageFlag ∧ ∃ i < pageCount pg, ownHas pages (branchPgid pg i) p) := by
  cases h with
  | root _ _ _ => exact Or.inl rfl
  | child _ pg' i _ hpg' hb hi h =>
    rw [hpg] at hpg'; cases hpg'
    exact Or.inr ⟨hb, i, hi, h⟩

theorem mat_ownHas_some {pages : Pages} {a b : Nat} (h : ownHas pages a b) :
    (pages !! a).isSome := by
  cases h with
  | root _ pg hpg => rw [hpg]; rfl
  | child _ pg _ _ hpg _ _ _ => rw [hpg]; rfl

section child2
variable (W : View) (hwm : Nat) (bl : Loc) (B : BRec) (hv : pagesStrict W.pages)
    (hc : bktClean W hwm bl B) (nl : Loc) (rp : NRec) (i : Nat) (w : WEntry)
    (hrp : B.ns !! nl = some rp) (hbr : rp.nv.isLeaf' = false) (hw : rp.ws[i]? = some w)
    (hnone : B.nm !! w.pgid = none) (l : Loc) (hfresh : B.ns !! l = none) (hl : l ≠ null)
    (pg : List w8) (hpg : W.pages !! w.pgid.toNat = some pg) (r rp' : NRec)
    (hr : matNew bl nl pg r) (hp' : matParent rp rp' l)
include hv hc hrp hbr hw hnone hfresh hl hpg hr hp'

/-- The new node's children are not materialized. -/
theorem mat_free : ∀ j < pageCount pg, pageFlags pg = branchPageFlag →
    (matBkt B w.pgid nl l rp' r).nm !! W64 (branchPgid pg j : Int) = none := by
  obtain ⟨-, -, -, -, -, -, -, hpt, hpos⟩ :=
    mat_basic W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  intro j hj hb
  rcases mat_kind hpt with ⟨h, -⟩ | ⟨-, -, hbk⟩
  · rw [h] at hb; exact absurd hb.symm mat_branch_ne_leaf
  cases hbk j hj with
  | page _ pgj _ _ hpgj _ _ _ =>
    have hcs := treeHas.root _ pgj hpgj
    rw [mat_nm, if_neg]
    · exact hc.2.2.2.2.2.2.2.2.2.1 nl i w.pgid hpos _ (mat_treeHas_child hpg hb j hj _ hcs)
    · intro he
      rw [mat_W64_eq_iff _ _ (mat_branchPgid_lt pg j)] at he
      exact (hv.2.1 _ pg hpg hb).2 j hj (by rw [← he]; exact hcs)

/-- An old node of the grown bucket: its old record and what it keeps. -/
theorem mat_old (y : Loc) (ry : NRec) (hy : (matBkt B w.pgid nl l rp' r).ns !! y = some ry)
    (hyl : y ≠ l) : ∃ ry0, B.ns !! y = some ry0 ∧
      ry.nv.parent' = ry0.nv.parent' ∧ ry.nv.isLeaf' = ry0.nv.isLeaf' ∧ ry.ws = ry0.ws ∧
      ry.nv.pgid' = ry0.nv.pgid' ∧ (∀ z ∈ ry0.cs, z ∈ ry.cs) ∧ ry.nv.key' = ry0.nv.key' ∧
      ry.key = ry0.key ∧ ry.nv.unbalanced' = ry0.nv.unbalanced' := by
  have hnsB := mat_nsB W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have h0 : ∃ ry0, B.ns !! y = some ry0 := by
    by_cases hyn : y = nl
    · exact ⟨rp, by rw [hyn]; exact hrp⟩
    · rw [mat_ns, if_neg hyl, if_neg hyn] at hy; exact ⟨ry, hy⟩
  obtain ⟨ry0, hry0⟩ := h0
  obtain ⟨ry', h1, rest⟩ := hnsB y ry0 hry0
  rw [h1] at hy; cases hy
  exact ⟨ry0, hry0, rest⟩

/-- Materializing the page position `w.pgid` (entry `i` of the branch node `nl`) keeps the
rebalance's keys, the new node's bounds its entry's. -/
theorem rblKeys_addChild (hx : matExtra r) (bnd : Loc → Option (List w8) × Option (List w8))
    (dfc : Option Loc) (hk : rblKeysB W B bnd dfc) :
    rblKeysB W (matBkt B w.pgid nl l rp' r)
      (fun x => if x = l then wEntryBnd (bnd nl) rp.ws i else bnd x) dfc := by
  obtain ⟨hroot, hrn, hnl, hlnl, hpgc, hcid, hwfc, hpt, hpos⟩ :=
    mat_basic W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hnsB := mat_nsB W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hold' := mat_old W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hfree := mat_free W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12⟩ := hr
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hp'
  obtain ⟨hk1, hk2, hk3⟩ := hk
  have hns' := mat_ns B w.pgid nl l rp' r
  have hnm' := mat_nm B w.pgid nl l rp' r
  obtain ⟨-, -, hrpk3, -, -⟩ := hk3 nl rp hrp
  obtain ⟨-, hrpfst, kind, hkd⟩ := hrpk3 hbr
  obtain ⟨pg', hpg', hcnt, -, hkey0, htk⟩ := (hkd i w hw).2 hnone
  rw [hpg] at hpg'; cases hpg'
  have hold : ∀ x, (B.ns !! x).isSome → x ≠ l := by
    intro x hx he; rw [he, hfresh] at hx; cases hx
  have hpar : ∀ y ry, B.ns !! y = some ry → ry.nv.parent' ≠ null →
      (B.ns !! ry.nv.parent').isSome := by
    intro y ry hy hp
    obtain ⟨rq, hrq, -⟩ := ncol_par (hc.2.2.2.2.2.2.2.1 y ry hy) hp
    rw [hrq]; rfl
  have hframe : ∀ y ry ry', B.ns !! y = some ry → ry'.ws = ry.ws →
      ry'.nv.parent' = ry.nv.parent' → ry'.nv.isLeaf' = ry.nv.isLeaf' → ry'.nv.key' = ry.nv.key' →
      ry'.key = ry.key → ry'.nv.pgid' = ry.nv.pgid' → ry'.nv.unbalanced' = ry.nv.unbalanced' →
      rblNodeKeys W (matBkt B w.pgid nl l rp' r)
        (fun x => if x = l then wEntryBnd (bnd nl) rp.ws i else bnd x) dfc y ry' := by
    intro y ry ry' hy h1 h2 h3 h4 h5 h6 h7
    refine rblNodeKeys_frame W B _ bnd _ dfc y ry ry' (hk3 y ry hy)
      (by rw [if_neg (hold y (by rw [hy]; rfl))])
      (fun hp => by rw [if_neg (hold _ (hpar y ry hy hp))]) h1 h2 h3 h4 h5 h6 h7 rfl
      (fun z rz hz => by
        obtain ⟨rz', a, -, b, c, -⟩ := hnsB z rz hz; exact ⟨rz', a, c, b⟩) ?_ ?_
    · intro k l' hl'
      rw [hnm'] at hl'
      split at hl'
      · rename_i hkw
        cases hl'
        subst hkw
        refine Or.inr ⟨hnone, _, by rw [hns', if_pos rfl], fun pg0 h0 => ?_⟩
        rw [hpg] at h0; cases h0; exact hr4
      · exact Or.inl hl'
    · intro k hk0
      rw [hnm'] at hk0
      split at hk0
      · cases hk0
      · exact hk0
  refine ⟨fun h => hk1 h, ?_, ?_⟩
  · intro r0 h0
    have hrs := hc.2.2.2.1 hrn
    obtain ⟨-, rr, hrr, -⟩ := hc.2.2.2.2.1 _ _ hrs
    change (matBkt B w.pgid nl l rp' r).ns !! B.bv.rootNode' = some r0 at h0
    obtain ⟨ry0, hry0, hpar0, -⟩ := hold' _ r0 h0 (hold _ (by rw [hrr]; rfl))
    rw [hpar0]; exact hk2 ry0 hry0
  · intro y ry hy
    by_cases hyl : y = l
    · rw [hns', if_pos hyl] at hy; cases hy
      have hnlb : (if nl = l then wEntryBnd (bnd nl) rp.ws i else bnd nl) = bnd nl := by
        rw [if_neg (Ne.symm hlnl)]
      have hyb : (if y = l then wEntryBnd (bnd nl) rp.ws i else bnd y) = wEntryBnd (bnd nl) rp.ws i := by
        rw [if_pos hyl]
      have hybF : (fun x => if x = l then wEntryBnd (bnd nl) rp.ws i else bnd x) y =
          wEntryBnd (bnd nl) rp.ws i := hyb
      have hk0 : r.key = w.key := by
        rw [hr11, mat_wKey hr9, mat_wKey_page pg 0 hcnt]; exact hkey0
      have htk' := mat_treeKeys_key _ _ _ _ pg htk hpg
      refine ⟨?_, fun _ => ⟨hx.2.1, ?_⟩, fun hlf => ?_, fun _ _ _ _ => by rw [mat_len hr9]; exact hcnt,
        fun hlf x hxm => ?_⟩
      · intro x hxm
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hxm
        obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
        show keyIn (if y = l then wEntryBnd (bnd nl) rp.ws i else bnd y).1
          (if y = l then wEntryBnd (bnd nl) rp.ws i else bnd y).2 x.key
        rw [hyb, (mat_wDat_eq hd).2.2.1, mat_pageW_key]; exact htk' j hjc
      · rw [hr2]
        refine ⟨rp', i, w, by rw [hns', if_neg (Ne.symm hlnl), if_pos rfl], by rw [hp2]; exact hw,
          by rw [hr3, hcid], hk0.symm, ?_⟩
        show bndIn (if y = l then wEntryBnd (bnd nl) rp.ws i else bnd y)
          (wEntryBnd (if nl = l then wEntryBnd (bnd nl) rp.ws i else bnd nl) rp'.ws i)
        rw [hyb, hnlb, hp2]; exact bndIn_refl _
      · have hnleaf : pageFlags pg ≠ leafPageFlag := by
          intro h; rw [hr4, h] at hlf; simp at hlf
        cases htk with
        | leaf _ pg' _ _ hpg' hl' _ _ => rw [hpg] at hpg'; cases hpg'; exact absurd hl' hnleaf
        | branch _ pg' _ _ kindN hpg' hbr' h2 _ hch hsub =>
          rw [hpg] at hpg'; cases hpg'
          refine ⟨fun _ => by rw [mat_len hr9]; exact h2, ?_, decide (kindN = leafPageFlag),
            fun j x hj => ?_⟩
          · intro x hx'
            rw [hybF] at hx'
            rw [mat_wKey hr9, mat_wKey_page pg 0 hcnt, hkey0]
            have hwk : (rp.ws.map WEntry.key).getD i [] = w.key := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_map, hw]; rfl
            unfold wEntryBnd entryBnd childLo at hx'
            by_cases hi0 : i = 0
            · rw [if_pos hi0] at hx'
              have := hrpfst x hx'
              subst hi0
              unfold wKey at this; rw [hw] at this; exact this
            · rw [if_neg hi0] at hx'; simp only [hwk] at hx'; cases hx'; rfl
          · obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
            obtain ⟨cpg, hcpg, hcc, hcf, hck⟩ := hch j hjc
            have hpj : x.pgid = W64 (branchPgid pg j : Int) := by
              rw [(mat_wDat_eq hd).2.1, (mat_pageW_branch pg j hnleaf).1]
            have hnm0 := hfree j hjc hbr'
            rw [← hpj] at hnm0
            refine ⟨fun l' hl' => (by rw [hnm0] at hl'; cases hl'), fun _ => ⟨cpg, ?_, hcc,
              by rw [hcf], ?_, ?_⟩⟩
            · rw [hpj, toNat_W64_of_lt _ (mat_branchPgid_lt pg j)]; exact hcpg
            · rw [hck, (mat_wDat_eq hd).2.2.1, (mat_pageW_branch pg j hnleaf).2]
            · rw [hpj, toNat_W64_of_lt _ (mat_branchPgid_lt pg j), mat_wEntryBnd hr9, hybF,
                mat_entryBnd_page _ pg j hjc hnleaf]
              exact hsub j hjc
      · have hfl : pageFlags pg = leafPageFlag := by rw [hr4] at hlf; simpa using hlf
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hxm
        obtain ⟨hjc, hd⟩ := mat_at hr9 j x hj
        obtain ⟨e1, e2, -, e4⟩ := mat_wDat_eq hd
        obtain ⟨f1, f2, -, f4⟩ := mat_pageW_leaf pg j hfl
        refine ⟨by rw [e2, f2], fun hbk h0 _ => ?_⟩
        rw [e1, f1, mat_isBktFlag_iff _ (mat_leafFlags_lt pg j)] at hbk
        rw [e4, f4] at h0 ⊢
        cases htk with
        | leaf _ pg' _ _ hpg' _ _ hbkt =>
          rw [hpg] at hpg'; cases hpg'
          exact hbkt j hjc hbk h0
        | branch _ pg' _ _ _ hpg' hbr' _ _ _ _ =>
          rw [hpg] at hpg'; cases hpg'
          rw [hfl] at hbr'; exact absurd hbr'.symm mat_branch_ne_leaf
    · obtain ⟨ry0, hry0, a1, a2, a3, a4, -, a6, a7, a8⟩ := hold' y ry hy hyl
      exact hframe y ry0 ry hry0 a3 a1 a2 a6 a7 a4 a8

theorem rblAcyc_addChild (ha : rblAcyc B) : rblAcyc (matBkt B w.pgid nl l rp' r) := by
  obtain ⟨-, -, -, hlnl, -⟩ :=
    mat_basic W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hold' := mat_old W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  obtain ⟨ht, hh⟩ := ha
  have hpar : ∀ y ry, B.ns !! y = some ry → ry.nv.parent' ≠ null → ry.nv.parent' ≠ l := by
    intro y ry hy hp he
    obtain ⟨rq, hrq, -⟩ := ncol_par (hc.2.2.2.2.2.2.2.1 y ry hy) hp
    rw [he, hfresh] at hrq; cases hrq
  refine ⟨fun x => if x = l then 0 else ht x + 1, fun y ry hy hp => ?_⟩
  by_cases hyl : y = l
  · rw [mat_ns, if_pos hyl] at hy; cases hy
    show (if y = l then 0 else ht y + 1) < (if r.nv.parent' = l then 0 else ht r.nv.parent' + 1)
    rw [if_pos hyl, hr.2.1, if_neg (Ne.symm hlnl)]; omega
  · obtain ⟨ry0, hry0, a1, -⟩ := hold' y ry hy hyl
    rw [a1] at hp ⊢
    have := hh y ry0 hry0 hp
    show (if y = l then 0 else ht y + 1) < (if ry0.nv.parent' = l then 0 else ht ry0.nv.parent' + 1)
    rw [if_neg hyl, if_neg (hpar y ry0 hry0 hp)]; omega

theorem rblHt_addChild (ha : rblHt W B) : rblHt W (matBkt B w.pgid nl l rp' r) := by
  obtain ⟨-, -, -, -, -, -, -, hpt, -⟩ :=
    mat_basic W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hold' := mat_old W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hfree := mat_free W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hnm' := mat_nm B w.pgid nl l rp' r
  obtain ⟨ht, pht, hp, hh⟩ := ha
  have hkind := mat_kind hpt
  have hold : ∀ y ry, B.ns !! y = some ry → y ≠ l := by
    intro y ry hy he; rw [he, hfresh] at hy; cases hy
  have hent : ∀ y ry, B.ns !! y = some ry → ry.nv.isLeaf' = false → ∀ w' ∈ ry.ws,
      (∀ l', (matBkt B w.pgid nl l rp' r).nm !! w'.pgid = some l' →
        (if l' = l then pht w.pgid.toNat else ht l') + 1 =
          (if y = l then pht w.pgid.toNat else ht y)) ∧
      ((matBkt B w.pgid nl l rp' r).nm !! w'.pgid = none →
        pht w'.pgid.toNat + 1 = (if y = l then pht w.pgid.toNat else ht y)) := by
    intro y ry hy hb w' hw'
    rw [if_neg (hold y ry hy)]
    obtain ⟨a1, a2⟩ := (hh y ry hy).2 hb w' hw'
    refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
    · rw [hnm'] at hl'
      split at hl'
      · rename_i he
        cases hl'
        rw [if_pos rfl, ← he]; exact a2 (by rw [he]; exact hnone)
      · obtain ⟨-, r0, hr0, -⟩ := hc.2.2.2.2.1 _ _ hl'
        rw [if_neg (hold l' r0 hr0)]; exact a1 l' hl'
    · rw [hnm'] at hn
      split at hn
      · cases hn
      · exact a2 hn
  refine ⟨fun x => if x = l then pht w.pgid.toNat else ht x, pht, hp, fun y ry hy => ?_⟩
  by_cases hyl : y = l
  · rw [mat_ns, if_pos hyl] at hy; cases hy
    have hpp := hp _ pg hpg
    refine ⟨fun hlf => ?_, fun hb => ?_⟩
    · have hl' : pageFlags pg = leafPageFlag := by rw [hr.2.2.2.1] at hlf; simpa using hlf
      show (if y = l then pht w.pgid.toNat else ht y) = 0
      rw [if_pos hyl]; exact hpp.1 hl'
    · have hnl' : pageFlags pg ≠ leafPageFlag := by
        intro h; rw [hr.2.2.2.1, h] at hb; simp at hb
      have hbr' : pageFlags pg = branchPageFlag := by
        rcases hkind with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd h hnl'
        · exact h
      intro x hx
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
      obtain ⟨hjc, hd⟩ := mat_at hr.2.2.2.2.2.2.2.2.1 j x hj
      have hpj : x.pgid = W64 (branchPgid pg j : Int) := by
        rw [(mat_wDat_eq hd).2.1, (mat_pageW_branch pg j hnl').1]
      have hn0 := hfree j hjc hbr'
      rw [← hpj] at hn0
      refine ⟨fun l' hl' => (by rw [hn0] at hl'; cases hl'), fun _ => ?_⟩
      show pht x.pgid.toNat + 1 = (if y = l then pht w.pgid.toNat else ht y)
      rw [if_pos hyl, hpj, toNat_W64_of_lt _ (mat_branchPgid_lt pg j)]
      exact hpp.2 hbr' j hjc
  · obtain ⟨ry0, hry0, -, a2, a3, -⟩ := hold' y ry hy hyl
    rw [a2, a3]
    refine ⟨fun hlf => ?_, fun hb => hent y ry0 hry0 hb⟩
    show (if y = l then pht w.pgid.toNat else ht y) = 0
    rw [if_neg hyl]; exact (hh y ry0 hry0).1 hlf

/-- An entry on a page of the materialized position: in the new node, or on a page of one of
its children's positions. -/
theorem entryIn_addChild (k v : List w8) (h : entryIn W B k v) :
    entryIn W (matBkt B w.pgid nl l rp' r) k v := by
  obtain ⟨-, hrn, -, -, -, -, -, -, -⟩ :=
    mat_basic W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hnsB := mat_nsB W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hfree := mat_free W hwm bl B hv hc nl rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr hp'
  have hnm' := mat_nm B w.pgid nl l rp' r
  have hrl : (matBkt B w.pgid nl l rp' r).ns !! l = some r := by rw [mat_ns, if_pos rfl]
  have hr4 := hr.2.2.2.1
  have hr9 := hr.2.2.2.2.2.2.2.2.1
  rcases h with ⟨y, ry, w', hy, hlf, hmem, hk, hbk, hvv⟩ |
    ⟨c', q, pgq, j, hpos', hown, hpq, hlq, hj, hkq, hfq, hvq⟩
  · obtain ⟨ry', h1, -, h3, h2, -⟩ := hnsB y ry hy
    exact Or.inl ⟨y, ry', w', h1, by rw [h3]; exact hlf, by rw [h2]; exact hmem, hk, hbk, hvv⟩
  · rcases hpos' with ⟨hrn0, -⟩ | ⟨y, j0, hpp, hlt⟩
    · exact absurd hrn0 hrn
    by_cases hce : W64 (c' : Int) = w.pgid
    · have hcn : c' = w.pgid.toNat := (mat_W64_eq_iff c' w.pgid hlt).1 hce
      subst hcn
      rcases mat_ownHas_cases pg hpg hown with rfl | ⟨hb, i', hi', hown'⟩
      · rw [hpg] at hpq; cases hpq
        obtain ⟨x, hx, hd⟩ := mat_at' hr9 j hj
        obtain ⟨e1, -, e3, e4⟩ := mat_wDat_eq hd
        obtain ⟨f1, -, f3, f4⟩ := mat_pageW_leaf _ j hlq
        refine Or.inl ⟨l, r, x, hrl, by rw [hr4]; simp [hlq], List.mem_of_getElem? hx,
          by rw [e3, f3]; exact hkq, ?_, by rw [e4, f4]; exact hvq⟩
        rw [e1, f1, mat_isBktFlag_iff _ (mat_leafFlags_lt _ j)]; exact hfq
      · have hnl : pageFlags pg ≠ leafPageFlag := by rw [hb]; exact mat_branch_ne_leaf
        obtain ⟨x, hx, hd⟩ := mat_at' hr9 i' hi'
        refine Or.inr ⟨branchPgid pg i', q, pgq, j, Or.inr ⟨l, i', ⟨r, x, hrl,
          by rw [hr4]; simp [hnl], hx, by rw [(mat_wDat_eq hd).2.1, (mat_pageW_branch pg i' hnl).1],
          hfree i' hi' hb⟩, mat_branchPgid_lt pg i'⟩, hown', hpq, hlq, hj, hkq, hfq, hvq⟩
    · obtain ⟨ry, wy, hy, hyl, hwy, hwyp, hnmy⟩ := hpp
      obtain ⟨ry', h1, -, h3, h2, -⟩ := hnsB y ry hy
      refine Or.inr ⟨c', q, pgq, j, Or.inr ⟨y, j0, ⟨ry', wy, h1, by rw [h3]; exact hyl,
        by rw [h2]; exact hwy, hwyp, ?_⟩, hlt⟩, hown, hpq, hlq, hj, hkq, hfq, hvq⟩
      rw [hnm', if_neg hce]; exact hnmy

end child2

/-- **A page position materialized during rebalance** (`b.node(pgid, parent)` with `pgid` the
unmaterialized entry `i` of the live branch node `parent`, `nodeAdded`): the bucket stays in the
rebalance's invariant (the same deficient node), the new node's bounds its entry's; the nested
buckets' entries stay; the bucket's struct, header and bucket cache are unchanged; the new node
`l` is cached at `pgid`, under `parent`; no node is newly unbalanced; every old node keeps its
entries, kind, parent, unbalanced flag and page id.

Beyond `nodeAdded`: the base view is well-formed (`viewWF`, `wOK`'s and `wOKR`'s; rebalance does
not change `X.v`), `l` was not a node of the bucket (`nodeAdded`'s `X.t.objs !! l = none` gives it:
`Write.objs_isSome_node`), and what `nodeAdded` leaves open (`matExtra` of the new node, the
parent's `capOwn`). -/
theorem rbl_nodeAdded (X X' : WX) (hwm : Nat) (bl l : Loc) (pgid : w64) (parent : Loc)
    (B : BRec) (dfc : Option Loc) (i : Nat) (hB : X.t.bs !! bl = some B) (hv : viewWF X.v)
    (HB : rblB X.v hwm bl B dfc) (hadd : nodeAdded X X' bl l pgid parent)
    (hpos : pagePosAt B parent i pgid) (hfresh : B.ns !! l = none) :
    ∃ B', X'.t.bs !! bl = some B' ∧ X'.v = X.v ∧ rblB X'.v hwm bl B' dfc ∧
      (∀ k v, entryIn X.v B k v → entryIn X'.v B' k v) ∧
      B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.bm = B.bm ∧ B'.nm !! pgid = some l ∧
      (∃ rl, B'.ns !! l = some rl ∧ rl.nv.parent' = parent) ∧
      (∀ y ry', B'.ns !! y = some ry' → ry'.nv.unbalanced' = true →
        ∃ ry, B.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧ ry'.nv.pgid' = ry.nv.pgid') ∧
      (∀ y ry, B.ns !! y = some ry → ∃ ry', B'.ns !! y = some ry' ∧ ry'.ws = ry.ws ∧
        ry'.nv.isLeaf' = ry.nv.isLeaf' ∧ ry'.nv.parent' = ry.nv.parent' ∧
        ry'.nv.unbalanced' = ry.nv.unbalanced' ∧ ry'.nv.pgid' = ry.nv.pgid') := by
  obtain ⟨hc, ⟨bnd, hk⟩, ha, hht⟩ := HB
  obtain ⟨rp, w, hrp, hbr, hw, rfl, hnone⟩ := hpos
  obtain ⟨B0, pa, pg, r, ns', bv', hB0, hwp, -, hl0, -, hrb, hrpar, hrid, hrleaf, hru, hrs, hrcs,
    hrco, hrws, hrlive, hrkey, hrks, hrins, hrkn, hrvs, hcase, hX'⟩ := hadd
  rw [hB] at hB0; cases hB0
  have hroot : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc.2.2.2.2.2.2.1 h0 parent rp hrp; rw [hbr] at this; cases this
  have hpnl : parent ≠ null := (hc.2.2.2.2.1 _ _ (ncol_nm (hc.2.2.2.2.2.2.2.1 parent rp hrp))).1
  have hpg : X.v.pages !! w.pgid.toNat = some pg := by
    unfold wpageAt at hwp; rw [if_neg hroot] at hwp
    cases h : X.v.pages !! w.pgid.toNat with
    | none => rw [h] at hwp; cases hwp
    | some pg0 => rw [h] at hwp; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hwp
                  rw [hwp.2]
  rcases hcase with ⟨hpn, -, -⟩ | ⟨-, hbv, rp0, rp', hrp0, -, hc1, hc2, hc3, hc4, hc5, hcp, hc6, hns⟩
  · exact absurd hpn hpnl
  rw [hrp] at hrp0; cases hrp0
  subst hbv; subst hns
  have hB' : X'.t.bs !! bl = some (matBkt B w.pgid parent l rp' r) := by
    rw [hX']; show (X.t.bs.insert bl _) !! bl = _; rw [GMap.lookup_insert]; rfl
  have hv' : X'.v = X.v := by rw [hX']
  have hrl : (matBkt B w.pgid parent l rp' r).ns !! l = some r := by rw [mat_ns, if_pos rfl]
  have hrp' : (matBkt B w.pgid parent l rp' r).ns !! parent = some rp' := by
    rw [mat_ns, if_neg (fun h => by rw [h, hfresh] at hrp; cases hrp), if_pos rfl]
  have hr : matNew bl parent pg r :=
    ⟨hrb, hrpar, hrid, hrleaf, hru, hrs, hrcs, hrco, by rw [hrws, mat_pageWsAs_wDat], hrlive,
      hrkey, hrks⟩
  have hp' : matParent rp rp' l := ⟨hc1, hc2, hc3, hc4, hc5, hc6, hcp⟩
  have hstrict := mat_strict X.v hv
  have hl : l ≠ null := hl0
  obtain ⟨-, -, hrpk3, -, -⟩ := hk.2.2 parent rp hrp
  obtain ⟨-, -, kind, hkd⟩ := hrpk3 hbr
  obtain ⟨pg', hpg', hcnt, -⟩ := (hkd i w hw).2 hnone
  rw [hpg] at hpg'; cases hpg'
  have hxr : matExtra r := by
    refine ⟨hrins, fun hn => ?_, hrvs⟩
    have h0 := hrkn.1 hn
    have := mat_len hr.2.2.2.2.2.2.2.2.1
    rw [h0] at this; simp only [List.length_nil] at this; omega
  have hnsB := mat_nsB X.v hwm bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl pg hpg
    r rp' hr hp'
  refine ⟨_, hB', hv', ?_, ?_, rfl, rfl, rfl, by rw [mat_nm, if_pos rfl], ⟨r, hrl, hrpar⟩, ?_, ?_⟩
  · rw [hv']
    exact ⟨mat_clean X.v hwm bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl pg hpg
        r rp' hr hp' hxr hcnt (Write.viewWF_leafInl X.v hv _ pg hpg) (viewWF_matNest X.v hv _ pg hpg),
      ⟨_, rblKeys_addChild X.v hwm bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl pg
        hpg r rp' hr hp' hxr bnd dfc hk⟩,
      rblAcyc_addChild X.v hwm bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl pg hpg
        r rp' hr hp' ha,
      rblHt_addChild X.v hwm bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl pg hpg
        r rp' hr hp' hht⟩
  · intro k v h
    rw [hv']
    exact entryIn_addChild X.v hwm bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl pg
      hpg r rp' hr hp' k v h
  · intro y ry' hy hu
    by_cases hyl : y = l
    · rw [mat_ns, if_pos hyl] at hy; cases hy; rw [hru] at hu; cases hu
    · obtain ⟨ry0, hry0, -, -, -, a4, -, -, -, a8⟩ :=
        mat_old X.v hwm bl B hstrict hc parent rp i w hrp hbr hw hnone l hfresh hl pg hpg r rp' hr
          hp' y ry' hy hyl
      exact ⟨ry0, hry0, by rw [← a8]; exact hu, a4⟩
  · intro y ry hy
    obtain ⟨ry', a1, a2, a3, a4, a5, -, -, -, a8⟩ := hnsB y ry hy
    exact ⟨ry', a1, a4, a3, a2, a8, a5⟩

end mat

end bbolt
end EtcdGrove
end Perennial
