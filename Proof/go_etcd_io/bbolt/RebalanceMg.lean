/-
Two siblings merged by `node.rebalance` (`ll`, `lr`: the children of the parent `pl` at its
entries `k`, `k + 1`): the right one's materialized children reparented to the left one, which
gets the right one's entries; the parent's entry for the right one removed (`del`,
`removeChild`), the right one dropped (`delete(b.nodes, ...)`, its page freed). The bucket
`mgBkt` stays clean, keeps its keys (the merged node's bounds the join of the two; the right
one's first child's bound is the right one's first key, `brFirst`), its parent pointers without
cycle, its heights (both siblings one below the parent: their children are of one kind), the
nested buckets' entries, and the tokens but the right one's page's.
-/
module

public import Proof.go_etcd_io.bbolt.RebalanceRm

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The nodes `ns` with the children of `a` reparented to `b`. -/
def reparent (ns : GMap Loc NRec) (a b : Loc) : GMap Loc NRec :=
  GMap.fmap (fun x => if x.nv.parent' = a then { x with nv := { x.nv with parent' := b } } else x) ns

/-- The materialized children of the entries `ws`, in order. -/
def kidsOf (B : BRec) (ws : List WEntry) : List Loc := ws.filterMap fun w => B.nm !! w.pgid

/-- The left node after the merge (its slices `sI`, `sC`). -/
def mgLeft (rl rr : NRec) (moved : List Loc) (sI sC : GoSlice) : NRec :=
  ⟨{ rl.nv with inodes' := sI, children' := sC }, rl.ins ++ rr.ins, rl.ws ++ rr.ws, rl.cs ++ moved,
    rl.key, rl.ksrc⟩

/-- The bucket after the merge of `lr` (page `pgid`) into `ll`, the parent `pl` now `rp'`, the
left node `rl'`. -/
def mgBkt (B : BRec) (pl ll lr : Loc) (pgid : w64) (rp' rl' : NRec) : BRec :=
  { B with nm := GMap.delete pgid B.nm, ns :=
    <[pl := rp']> (<[ll := rl']> (reparent (GMap.delete lr B.ns) lr ll)) }

theorem reparent_lookup (ns : GMap Loc NRec) (a b y : Loc) :
    (reparent ns a b) !! y = (ns !! y).map
      (fun x => if x.nv.parent' = a then { x with nv := { x.nv with parent' := b } } else x) := by
  unfold reparent; rw [GMap.lookup_fmap]

theorem mg_ns (B : BRec) (pl ll lr : Loc) (pgid : w64) (rp' rl' : NRec) (y : Loc) :
    (mgBkt B pl ll lr pgid rp' rl').ns !! y =
      if y = pl then some rp' else if y = ll then some rl' else if y = lr then none else
        (B.ns !! y).map
          (fun x => if x.nv.parent' = lr then { x with nv := { x.nv with parent' := ll } } else x) := by
  show (<[pl := rp']> (<[ll := rl']> (reparent (GMap.delete lr B.ns) lr ll))) !! y = _
  rw [rf_lookup, rf_lookup, reparent_lookup]
  split
  · rfl
  · split
    · rfl
    · by_cases h : y = lr
      · subst h; rw [if_pos rfl, GMap.lookup_delete]; rfl
      · rw [if_neg h, GMap.lookup_delete_ne _ (Ne.symm h)]

theorem mg_nm (B : BRec) (pl ll lr : Loc) (pgid : w64) (rp' rl' : NRec) (k : w64) :
    (mgBkt B pl ll lr pgid rp' rl').nm !! k = if k = pgid then none else B.nm !! k := by
  show (GMap.delete pgid B.nm) !! k = _
  split
  · rename_i h; subst h; rw [GMap.lookup_delete]
  · rw [GMap.lookup_delete_ne _ (Ne.symm ‹_›)]

/-- Where a page position of the merged bucket was. -/
def mgPos (pl ll lr : Loc) (k nl : Nat) (y : Loc) (j : Nat) : Loc × Nat :=
  if y = pl then (pl, if j < k + 1 then j else j + 1)
  else if y = ll then (if j < nl then (ll, j) else (lr, j - nl)) else (y, j)

theorem mgPos_inj (pl ll lr : Loc) (k nl : Nat) (hlp : ll ≠ pl) (hrp : lr ≠ pl) (hlr : ll ≠ lr)
    (y1 y2 : Loc) (j1 j2 : Nat) (h1 : y1 ≠ lr) (h2 : y2 ≠ lr)
    (he : mgPos pl ll lr k nl y1 j1 = mgPos pl ll lr k nl y2 j2) : (y1, j1) = (y2, j2) := by
  unfold mgPos at he
  have side : ∀ (y : Loc) (j : Nat), y ≠ pl → y ≠ lr →
      ((if y = ll then (if j < nl then (ll, j) else (lr, j - nl)) else (y, j)) : Loc × Nat).1 ≠ pl := by
    intro y j hy hyr
    by_cases b : y = ll
    · rw [if_pos b]; by_cases c : j < nl
      · rw [if_pos c]; exact hlp
      · rw [if_neg c]; exact hrp
    · rw [if_neg b]; exact hy
  by_cases a1 : y1 = pl <;> by_cases a2 : y2 = pl
  · rw [if_pos a1, if_pos a2] at he
    have h := (Prod.mk.inj he).2
    rw [a1, a2]
    by_cases c1 : j1 < k + 1 <;> by_cases c2 : j2 < k + 1
    · rw [if_pos c1, if_pos c2] at h; rw [h]
    · rw [if_pos c1, if_neg c2] at h; omega
    · rw [if_neg c1, if_pos c2] at h; omega
    · rw [if_neg c1, if_neg c2] at h; rw [show j1 = j2 by omega]
  · rw [if_pos a1, if_neg a2] at he
    exact absurd (Prod.mk.inj he).1.symm (side y2 j2 a2 h2)
  · rw [if_neg a1, if_pos a2] at he
    exact absurd (Prod.mk.inj he).1 (side y1 j1 a1 h1)
  · rw [if_neg a1, if_neg a2] at he
    by_cases b1 : y1 = ll <;> by_cases b2 : y2 = ll
    · rw [if_pos b1, if_pos b2] at he
      rw [b1, b2]
      by_cases c1 : j1 < nl <;> by_cases c2 : j2 < nl
      · rw [if_pos c1, if_pos c2] at he; rw [(Prod.mk.inj he).2]
      · rw [if_pos c1, if_neg c2] at he; exact absurd (Prod.mk.inj he).1 hlr
      · rw [if_neg c1, if_pos c2] at he; exact absurd (Prod.mk.inj he).1 (Ne.symm hlr)
      · rw [if_neg c1, if_neg c2] at he; have := (Prod.mk.inj he).2; rw [show j1 = j2 by omega]
    · rw [if_pos b1, if_neg b2] at he
      by_cases c1 : j1 < nl
      · rw [if_pos c1] at he; exact absurd (Prod.mk.inj he).1.symm b2
      · rw [if_neg c1] at he; exact absurd (Prod.mk.inj he).1.symm h2
    · rw [if_neg b1, if_pos b2] at he
      by_cases c2 : j2 < nl
      · rw [if_pos c2] at he; exact absurd (Prod.mk.inj he).1 b1
      · rw [if_neg c2] at he; exact absurd (Prod.mk.inj he).1 h1
    · rw [if_neg b1, if_neg b2] at he; exact he

theorem wKey_append_left (L R : List WEntry) (j : Nat) (hj : j < L.length) :
    wKey (L ++ R) j = wKey L j := by
  unfold wKey; rw [List.getElem?_append_left hj]

theorem wKey_append_right (L R : List WEntry) (j : Nat) :
    wKey (L ++ R) (L.length + j) = wKey R j := by
  unfold wKey; rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-- The bounds of the left node's entries, in the merged node. -/
theorem entryBnd_left (bl b' : Option (List w8) × Option (List w8)) (L R : List WEntry) (j : Nat)
    (hj : j < L.length) (hlo : b'.1 = bl.1)
    (hR : ∀ y, wKey R 0 = y → R ≠ [] → ∃ x, bl.2 = some x ∧ ¬ go.GoStringLt y x)
    (hhi : ∀ y, b'.2 = some y → ∃ x, bl.2 = some x ∧ ¬ go.GoStringLt y x) :
    bndIn (entryBnd bl L j) (entryBnd b' (L ++ R) j) := by
  unfold entryBnd childLo childHi
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · simp only at hy ⊢
    by_cases h0 : j = 0
    · rw [if_pos h0] at hy ⊢; rw [hlo] at hy; exact ⟨y, hy, rk_le_refl y⟩
    · rw [if_neg h0] at hy ⊢; cases hy; rw [wKey_append_left L R j hj]; exact ⟨_, rfl, rk_le_refl _⟩
  · simp only at hy ⊢
    rw [List.length_append] at hy
    by_cases h1 : j + 1 < L.length
    · rw [if_pos (by omega)] at hy; cases hy
      rw [if_pos h1, wKey_append_left L R _ h1]; exact ⟨_, rfl, rk_le_refl _⟩
    · rw [if_neg h1]
      by_cases h2 : j + 1 < L.length + R.length
      · rw [if_pos h2] at hy; cases hy
        have : j + 1 = L.length + 0 := by omega
        rw [this, wKey_append_right]
        exact hR _ rfl (by intro h; rw [h] at h2; simp at h2; omega)
      · rw [if_neg h2] at hy; exact hhi y hy

/-- The bounds of the right node's entries, in the merged node. -/
theorem entryBnd_right (br b' : Option (List w8) × Option (List w8)) (L R : List WEntry) (j : Nat)
    (hj : j < R.length) (hL : 0 < L.length)
    (hlo : ∃ x, br.1 = some x ∧ ¬ go.GoStringLt x (wKey R 0))
    (hhi : ∀ y, b'.2 = some y → ∃ x, br.2 = some x ∧ ¬ go.GoStringLt y x) :
    bndIn (entryBnd br R j) (entryBnd b' (L ++ R) (L.length + j)) := by
  unfold entryBnd childLo childHi
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · simp only at hy ⊢
    rw [if_neg (by omega)] at hy; cases hy
    rw [wKey_append_right]
    by_cases h0 : j = 0
    · rw [if_pos h0]; subst h0; exact hlo
    · rw [if_neg h0]; exact ⟨_, rfl, rk_le_refl _⟩
  · simp only at hy ⊢
    rw [List.length_append] at hy
    by_cases h1 : j + 1 < R.length
    · rw [if_pos (by omega)] at hy; cases hy
      rw [if_pos h1, show L.length + j + 1 = L.length + (j + 1) by omega, wKey_append_right]
      exact ⟨_, rfl, rk_le_refl _⟩
    · rw [if_neg (by omega)] at hy
      rw [if_neg h1]; exact hhi y hy

/-- With heights, whether a branch's children are leaves is its height (one). -/
theorem kidLeaf (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (ht : Loc → Nat) (pht : Nat → Nat) (hp : pageHts W.pages pht)
    (hh : ∀ l r, B.ns !! l = some r → (r.nv.isLeaf' = true → ht l = 0) ∧
      (r.nv.isLeaf' = false → ∀ w ∈ r.ws, (∀ l', B.nm !! w.pgid = some l' → ht l' + 1 = ht l) ∧
        (B.nm !! w.pgid = none → pht (uint.nat w.pgid) + 1 = ht l)))
    (y : Loc) (ry : NRec) (hy : B.ns !! y = some ry) (hb : ry.nv.isLeaf' = false) (x : WEntry)
    (hx : x ∈ ry.ws) :
    (∀ l' r', B.nm !! x.pgid = some l' → B.ns !! l' = some r' → r'.nv.isLeaf' = decide (ht y = 1)) ∧
    (B.nm !! x.pgid = none → ∀ pg, W.pages !! uint.nat x.pgid = some pg → 0 < pageCount pg →
      decide (pageFlags pg = leafPageFlag) = decide (ht y = 1)) := by
  obtain ⟨a1, a2⟩ := (hh y ry hy).2 hb x hx
  refine ⟨fun l' r' hl' hr' => ?_, fun hn pg hpg hcnt => ?_⟩
  · have e := a1 l' hl'
    rcases (Bool.eq_false_or_eq_true r'.nv.isLeaf').symm with h | h
    · -- a branch child: it has a child, so its height is positive
      have hcl := (hc.2.2.2.2.2.2.2.1 l' r' hr').2.2.2.2.2.2.2.2.2.2.2.1 h
      obtain ⟨x', hx'⟩ : ∃ x', x' ∈ r'.ws := List.exists_mem_of_length_pos hcl.1
      obtain ⟨b1, b2⟩ := (hh l' r' hr').2 h x' hx'
      have hpos : 0 < ht l' := by
        cases hk : B.nm !! x'.pgid with
        | some l2 => have := b1 l2 hk; omega
        | none => have := b2 hk; omega
      rw [h]; symm; simp only [decide_eq_false_iff_not]; omega
    · rw [h]; symm; simp only [decide_eq_true_eq]
      have := (hh l' r' hr').1 h; omega
  · have e := a2 hn
    have hwf := (((hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.1 hb).2.2 x hx).2.2 hn
    obtain ⟨-, -, -, hk⟩ := treeWF_page _ _ _ pg hwf hpg
    obtain ⟨p1, p2⟩ := hp _ pg hpg
    rcases hk with ⟨hl, -⟩ | ⟨hbp, -⟩
    · rw [decide_eq_true hl]; symm; simp only [decide_eq_true_eq]; have := p1 hl; omega
    · have hnl : pageFlags pg ≠ leafPageFlag := by rw [hbp]; exact branch_ne_leaf
      rw [decide_eq_false hnl]; symm; simp only [decide_eq_false_iff_not]
      have := p2 hbp 0 hcnt; omega

theorem entryBnd_mid (b : Option (List w8) × Option (List w8)) (ws : List WEntry) (k : Nat)
    (w : WEntry) (h : ws[k + 1]? = some w) :
    (entryBnd b ws k).2 = some w.key ∧ (entryBnd b ws (k + 1)).1 = some w.key := by
  have hl := (List.getElem?_eq_some_iff.1 h).1
  have hk : wKey ws (k + 1) = w.key := by unfold wKey; rw [h]; rfl
  unfold entryBnd childLo childHi
  simp only
  rw [if_pos hl, if_neg (by omega), hk]; exact ⟨rfl, rfl⟩

/-- The merged node's bounds: the left one's low (its entry's, a leaf), the right one's entry's
high. -/
def mgBnd (bnd : Loc → Option (List w8) × Option (List w8)) (pl ll : Loc) (rp rl : NRec) (k : Nat) :
    Loc → Option (List w8) × Option (List w8) :=
  fun x => if x = ll then ((if rl.nv.isLeaf' then (entryBnd (bnd pl) rp.ws k).1 else (bnd ll).1),
    (entryBnd (bnd pl) rp.ws (k + 1)).2) else bnd x

section mg
variable (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (pl : Loc) (rp : NRec) (k : Nat)
  (wl wr : WEntry) (ll lr : Loc) (rl rr : NRec)
  (hc : bktClean W hwm bl B) (ha : rblAcyc B) (hpn : pl ≠ null) (hrp : B.ns !! pl = some rp)
  (hbr : rp.nv.isLeaf' = false)
  (hwl : rp.ws[k]? = some wl) (hwr : rp.ws[k + 1]? = some wr)
  (hll : B.nm !! wl.pgid = some ll) (hlr : B.nm !! wr.pgid = some lr)
  (hrl : B.ns !! ll = some rl) (hrr : B.ns !! lr = some rr)
include hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr

theorem mg_basic :
    rl.nv.parent' = pl ∧ rr.nv.parent' = pl ∧ ll ≠ lr ∧ ll ≠ pl ∧ lr ≠ pl ∧
      rl.nv.pgid' = wl.pgid ∧ rr.nv.pgid' = wr.pgid ∧ B.nm !! rp.nv.pgid' = some pl ∧
      (rp.ws.map WEntry.pgid).Nodup ∧ B.ib.root' ≠ W64 0 ∧ ll ∈ rp.cs ∧ lr ∈ rp.cs ∧
      (∀ y ry, B.ns !! y = some ry → ry.nv.parent' ≠ null → ry.nv.parent' ≠ y) ∧
      wl.pgid ≠ wr.pgid ∧ rp.nv.parent' ≠ pl := by
  have hnp := hc.2.2.2.2.2.2.2.1 pl rp hrp
  obtain ⟨-, hnd, hkids⟩ := hnp.2.2.2.2.2.2.2.2.2.2.2.1 hbr
  obtain ⟨r1, hr1, hp1⟩ := (hkids wl (List.mem_of_getElem? hwl)).2.1 ll hll
  rw [hrl] at hr1; cases hr1
  obtain ⟨r2, hr2, hp2⟩ := (hkids wr (List.mem_of_getElem? hwr)).2.1 lr hlr
  rw [hrr] at hr2; cases hr2
  have hpg : wl.pgid ≠ wr.pgid := nodup_pgid_ne rp.ws hnd (k + 1) k wr wl hwr hwl (by omega)
  obtain ⟨-, r3, hr3, hp3⟩ := hc.2.2.2.2.1 _ _ hll
  rw [hrl] at hr3; cases hr3
  obtain ⟨-, r4, hr4, hp4⟩ := hc.2.2.2.2.1 _ _ hlr
  rw [hrr] at hr4; cases hr4
  obtain ⟨ht, hh⟩ := ha
  have hself : ∀ y ry, B.ns !! y = some ry → ry.nv.parent' ≠ null → ry.nv.parent' ≠ y := by
    intro y ry hy hp he
    have := hh y ry hy hp; rw [he] at this; omega
  have hllr : ll ≠ lr := by
    intro he; subst he; rw [hrl] at hrr; cases hrr; exact hpg (hp3.symm.trans hp4)
  have hllp : ll ≠ pl := by
    intro he; subst he; rw [hrl] at hrp; cases hrp; exact hself _ _ hrl (by rw [hp1]; exact hpn) hp1
  have hlrp : lr ≠ pl := by
    intro he; subst he; rw [hrr] at hrp; cases hrp; exact hself _ _ hrr (by rw [hp2]; exact hpn) hp2
  have hin : ∀ y ry, B.ns !! y = some ry → ry.nv.parent' = pl → y ∈ rp.cs := by
    intro y ry hy hp
    obtain ⟨rq, hrq, -, hiq, -⟩ := (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [hp]; exact hpn)
    rw [hp, hrp] at hrq; cases hrq; exact hiq
  have hroot0 : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc.2.2.2.2.2.2.1 h0 pl rp hrp; rw [hbr] at this; cases this
  refine ⟨hp1, hp2, hllr, hllp, hlrp, hp3, hp4, hnp.2.2.2.2.2.2.1, hnd, hroot0, hin ll rl hrl hp1,
    hin lr rr hrr hp2, hself, hpg, ?_⟩
  intro he
  exact hself pl rp hrp (by rw [he]; exact hpn) he

/-- A child of either sibling is not their parent. -/
theorem mg_cyc (y : Loc) (ry : NRec) (hy : B.ns !! y = some ry)
    (hp : ry.nv.parent' = ll ∨ ry.nv.parent' = lr) : y ≠ pl := by
  obtain ⟨hp1, hp2, -⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have hlln : ll ≠ null := (hc.2.2.2.2.1 _ _ hll).1
  have hlrn : lr ≠ null := (hc.2.2.2.2.1 _ _ hlr).1
  intro he; subst he
  rw [hrp] at hy; cases hy
  obtain ⟨ht, hh⟩ := ha
  rcases hp with h | h
  · have h1 := hh ll rl hrl (by rw [hp1]; exact hpn)
    have h2 := hh _ rp hrp (by rw [h]; exact hlln)
    rw [hp1] at h1; rw [h] at h2; omega
  · have h1 := hh lr rr hrr (by rw [hp2]; exact hpn)
    have h2 := hh _ rp hrp (by rw [h]; exact hlrn)
    rw [hp2] at h1; rw [h] at h2; omega

/-- The only entry naming the right node's page is the parent's `k + 1`. -/
theorem mg_only (y : Loc) (ry : NRec) (j : Nat) (x : WEntry) (hy : B.ns !! y = some ry)
    (hb : ry.nv.isLeaf' = false) (hj : ry.ws[j]? = some x) (hx : x.pgid = wr.pgid) :
    y = pl ∧ j = k + 1 := by
  obtain ⟨hp1, hp2, -, -, -, -, -, -, hnd, -⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  obtain ⟨-, -, hk⟩ := (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.1 hb
  obtain ⟨-, hs, -⟩ := hk x (List.mem_of_getElem? hj)
  rw [hx] at hs
  obtain ⟨r1, hr1, hpr⟩ := hs lr hlr
  rw [hrr] at hr1; cases hr1
  rw [hp2] at hpr; subst hpr
  rw [hrp] at hy; cases hy
  refine ⟨rfl, ?_⟩
  by_cases hji : j = k + 1
  · exact hji
  · exact absurd (by rw [hx]) (nodup_pgid_ne rp.ws hnd (k + 1) j wr x hwr hj hji)

include hc in
theorem mg_moved (hleaf0 : rr.nv.isLeaf' = true → ∀ w ∈ rr.ws, B.nm !! w.pgid = none) :
    (∀ c, c ∈ kidsOf B rr.ws ↔ ∃ rc, B.ns !! c = some rc ∧ rc.nv.parent' = lr) ∧
      (kidsOf B rr.ws).Nodup := by
  have hnr := hc.2.2.2.2.2.2.2.1 lr rr hrr
  refine ⟨fun c => ⟨fun hcm => ?_, fun ⟨rc, hrc, hpc⟩ => ?_⟩, ?_⟩
  · obtain ⟨x, hx, hxc⟩ := List.mem_filterMap.1 hcm
    rcases (Bool.eq_false_or_eq_true rr.nv.isLeaf').symm with hb | hb
    · obtain ⟨-, -, hk⟩ := hnr.2.2.2.2.2.2.2.2.2.2.2.1 hb
      exact (hk x hx).2.1 c hxc
    · rw [hleaf0 hb x hx] at hxc; cases hxc
  · have hcn := hc.2.2.2.2.2.2.2.1 c rc hrc
    have hlrn : lr ≠ null := (hc.2.2.2.2.1 _ _ hlr).1
    obtain ⟨rq, hrq, -, -, x, hx, hxp⟩ := hcn.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by rw [hpc]; exact hlrn)
    rw [hpc, hrr] at hrq; cases hrq
    exact List.mem_filterMap.2 ⟨x, hx, by rw [hxp]; exact hcn.2.2.2.2.2.2.1⟩
  · rcases (Bool.eq_false_or_eq_true rr.nv.isLeaf').symm with hb | hb
    · obtain ⟨-, hnd, -⟩ := hnr.2.2.2.2.2.2.2.2.2.2.2.1 hb
      unfold kidsOf
      have key : ∀ (l : List WEntry), (l.map WEntry.pgid).Nodup →
          (l.filterMap fun w => B.nm !! w.pgid).Nodup := by
        intro l
        induction l with
        | nil => intro _; exact List.nodup_nil
        | cons x xs ih =>
          intro hn
          rw [List.map_cons, List.nodup_cons] at hn
          rw [List.filterMap_cons]
          cases hx : B.nm !! x.pgid with
          | none => exact ih hn.2
          | some b =>
            refine List.nodup_cons.2 ⟨fun hb' => ?_, ih hn.2⟩
            obtain ⟨y, hy, hyb⟩ := List.mem_filterMap.1 hb'
            have := nm_inj W hwm bl B hc _ _ _ hx hyb
            exact hn.1 (List.mem_map.2 ⟨y, hy, this.symm⟩)
      exact key _ hnd
    · have : kidsOf B rr.ws = [] := by
        unfold kidsOf; rw [List.filterMap_eq_nil_iff]; exact hleaf0 hb
      rw [this]; exact List.nodup_nil

include hc in
/-- The new record of an old node other than the parent, the siblings. -/
theorem mg_other (sI sC sI' sC' : GoSlice) (y : Loc) (ry : NRec) (hy : B.ns !! y = some ry)
    (hyp : y ≠ pl) (hyl : y ≠ ll) (hyr : y ≠ lr) :
    (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns !! y =
      some (if ry.nv.parent' = lr then { ry with nv := { ry.nv with parent' := ll } } else ry) := by
  rw [mg_ns, if_neg hyp, if_neg hyl, if_neg hyr, hy]; rfl

/-- Where a node of the bucket after the merge points to: an old node's new record. -/
theorem mg_look (sI sC sI' sC' : GoSlice) (y : Loc) (ry : NRec) (hy : B.ns !! y = some ry)
    (hyr : y ≠ lr) :
    ∃ ry', (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns !! y = some ry' ∧
      ry'.nv.pgid' = ry.nv.pgid' ∧ ry'.nv.isLeaf' = ry.nv.isLeaf' ∧
      ry'.nv.parent' = (if ry.nv.parent' = lr then ll else ry.nv.parent') := by
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, -, -, -, -, -, -, -, hself, -, hnself⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  by_cases hyp : y = pl
  · subst y; rw [hrp] at hy; cases hy
    refine ⟨rmParent rp (k + 1) lr sI' sC', by rw [mg_ns, if_pos rfl], rfl, rfl, ?_⟩
    have : rp.nv.parent' ≠ lr := fun he => mg_cyc W hwm bl B _ rp k wl wr ll lr rl rr hc ha hpn hrp hbr
      hwl hwr hll hlr hrl hrr _ rp hrp (Or.inr he) rfl
    rw [if_neg this]; rfl
  by_cases hyl : y = ll
  · subst y; rw [hrl] at hy; cases hy
    refine ⟨mgLeft rl rr (kidsOf B rr.ws) sI sC, by rw [mg_ns, if_neg hyp, if_pos rfl], rfl, rfl, ?_⟩
    rw [if_neg (by rw [hp1]; exact Ne.symm hlrp)]; rfl
  rw [mg_other W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
    sI sC sI' sC' y ry hy hyp hyl hyr]
  refine ⟨_, rfl, ?_, ?_, ?_⟩ <;> split <;> rfl

theorem mg_pos (sI sC sI' sC' : GoSlice) (hkind : rl.nv.isLeaf' = rr.nv.isLeaf') (y : Loc) (j : Nat) (c : w64)
    (hp : pagePosAt (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)) y j c) :
    y ≠ lr ∧ pagePosAt B (mgPos pl ll lr k rl.ws.length y j).1 (mgPos pl ll lr k rl.ws.length y j).2 c := by
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, hpgl, hpgr, -⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have honly := mg_only W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  obtain ⟨ry', x, hy, hb, hx, hxc, hn⟩ := hp
  rw [mg_nm] at hn
  have hcn : c ≠ rr.nv.pgid' := by
    intro he; rw [if_pos he] at hn; clear hn
    have hxp : x.pgid = wr.pgid := by rw [hxc, he, hpgr]
    rw [mg_ns] at hy
    split at hy
    · rename_i hyp; cases hy
      obtain ⟨j', hj'i, hj'⟩ := List.mem_eraseIdx_iff_getElem?.1 (List.mem_of_getElem? hx)
      exact hj'i (honly pl rp j' x hrp hbr hj' hxp).2
    split at hy
    · cases hy
      rcases List.mem_append.1 (List.mem_of_getElem? hx) with h | h
      · obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1 h
        exact hllp (honly ll rl j' x hrl hb hj' hxp).1
      · obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1 h
        exact hlrp (honly lr rr j' x hrr (by rw [← hkind]; exact hb) hj' hxp).1
    split at hy
    · cases hy
    · rename_i hyp _ _
      obtain ⟨ry, hry, rfl⟩ := Option.map_eq_some_iff.1 hy
      obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1 (List.mem_of_getElem? hx)
      have hb' : ry.nv.isLeaf' = false := by split at hb <;> exact hb
      have hx' : ry.ws[j]? = some x := by split at hx <;> exact hx
      exact hyp (honly y ry j x hry hb' hx' hxp).1
  rw [if_neg hcn] at hn
  rw [mg_ns] at hy
  unfold mgPos
  split at hy
  · rename_i hyp; cases hy; subst y
    refine ⟨Ne.symm hlrp, ?_⟩
    simp only [↓reduceIte]
    refine ⟨rp, x, hrp, hbr, ?_, hxc, hn⟩
    rw [← getElem?_eraseIdx']; exact hx
  rename_i hyp
  split at hy
  · rename_i hyl; cases hy; subst y
    refine ⟨hllr, ?_⟩
    simp only [hyp, ↓reduceIte]
    have hx2 : (rl.ws ++ rr.ws)[j]? = some x := hx
    split
    · rename_i hj
      exact ⟨rl, x, hrl, hb, by rw [List.getElem?_append_left hj] at hx2; exact hx2, hxc, hn⟩
    · rename_i hj
      exact ⟨rr, x, hrr, by rw [← hkind]; exact hb,
        by rw [List.getElem?_append_right (by omega)] at hx2; exact hx2, hxc, hn⟩
  rename_i hyl
  split at hy
  · cases hy
  rename_i hyr
  refine ⟨hyr, ?_⟩
  simp only [hyp, hyl, ↓reduceIte]
  obtain ⟨ry, hry, rfl⟩ := Option.map_eq_some_iff.1 hy
  have hb' : ry.nv.isLeaf' = false := by split at hb <;> exact hb
  have hx' : ry.ws[j]? = some x := by split at hx <;> exact hx
  exact ⟨ry, x, hry, hb', hx', hxc, hn⟩

/-- The siblings' bounds, from the keys: inside their entries'. -/
theorem mg_bnds (bnd : Loc → Option (List w8) × Option (List w8)) (dfc : Option Loc)
    (hk : rblKeysB W B bnd dfc) :
    bndIn (bnd ll) (entryBnd (bnd pl) rp.ws k) ∧ bndIn (bnd lr) (entryBnd (bnd pl) rp.ws (k + 1)) := by
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, hpgl, hpgr, -, hnd, -⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  constructor
  · obtain ⟨-, rq, i, x, hrq, hx, hxp, -, hb⟩ := (hk.2.2 ll rl hrl).2.1 (by rw [hp1]; exact hpn)
    rw [hp1, hrp] at hrq; cases hrq
    have : i = k := by
      by_cases h : i = k
      · exact h
      · exact absurd (by rw [hxp, hpgl]) (nodup_pgid_ne rp.ws hnd k i wl x hwl hx h)
    subst this; rw [hp1] at hb; exact hb
  · obtain ⟨-, rq, i, x, hrq, hx, hxp, -, hb⟩ := (hk.2.2 lr rr hrr).2.1 (by rw [hp2]; exact hpn)
    rw [hp2, hrp] at hrq; cases hrq
    have : i = k + 1 := by
      by_cases h : i = k + 1
      · exact h
      · exact absurd (by rw [hxp, hpgr]) (nodup_pgid_ne rp.ws hnd (k + 1) i wr x hwr hx h)
    subst this; rw [hp2] at hb; exact hb

/-- The keys of the left node are below those of the right one. -/
theorem mg_lt (bnd : Loc → Option (List w8) × Option (List w8)) (dfc : Option Loc)
    (hk : rblKeysB W B bnd dfc) : ∀ x ∈ rl.ws, ∀ y ∈ rr.ws, go.GoStringLt x.key y.key := by
  obtain ⟨hbl, hbr'⟩ := mg_bnds W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr
    hrl hrr bnd dfc hk
  obtain ⟨e1, e2⟩ := entryBnd_mid (bnd pl) rp.ws k wr hwr
  intro x hx y hy
  have kx := (hk.2.2 ll rl hrl).1 x hx
  have ky := (hk.2.2 lr rr hrr).1 y hy
  obtain ⟨xh, hxh, hxh'⟩ := hbl.2 _ e1
  obtain ⟨yl, hyl, hyl'⟩ := hbr'.1 _ e2
  have h1 := kx.2 xh hxh
  have h2 := ky.1 yl hyl
  exact rk_lt_of_lt_le (rk_lt_of_lt_le h1 hxh') (rk_le_trans hyl' h2)

theorem mg_clean (sI sC sI' sC' : GoSlice) (hkind : rl.nv.isLeaf' = rr.nv.isLeaf')
    (hlt : ∀ x ∈ rl.ws, ∀ y ∈ rr.ws, go.GoStringLt x.key y.key)
    (hleaf0 : rr.nv.isLeaf' = true → ∀ w ∈ rr.ws, B.nm !! w.pgid = none)
    (hroot : B.bv.rootNode' ≠ lr) :
    bktClean W hwm bl (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)) := by
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, hpgl, hpgr, hnmp, hnd, hroot0, hinl, hinr, hself, hpgne, hnself⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  obtain ⟨hmv, hmnd⟩ := mg_moved W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr
    hrl hrr hleaf0
  have hcyc := mg_cyc W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have honly := mg_only W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have hlook := mg_look W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
    sI sC sI' sC'
  have hother := mg_other W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
    sI sC sI' sC'
  have hnm' := mg_nm B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
    (mgLeft rl rr (kidsOf B rr.ws) sI sC)
  have hns' := mg_ns B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
    (mgLeft rl rr (kidsOf B rr.ws) sI sC)
  have hinj := nm_inj W hwm bl B hc
  have hcl := hc
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hcl
  have hrn : B.bv.rootNode' ≠ null := by
    intro h0; have := (c3 h0).1; rw [this] at hrp; cases hrp
  have hnp := c8 pl rp hrp
  have hnl := c8 ll rl hrl
  have hnr := c8 lr rr hrr
  have hil : k + 1 < rp.ws.length := (List.getElem?_eq_some_iff.1 hwr).1
  have hilen : rp.ins.length = rp.ws.length := hnp.2.1
  have hnmr : B.nm !! rr.nv.pgid' = some lr := by rw [hpgr]; exact hlr
  have hnml : B.nm !! rl.nv.pgid' = some ll := by rw [hpgl]; exact hll
  have hpgr' : rr.nv.pgid' ≠ rl.nv.pgid' := by rw [hpgr, hpgl]; exact Ne.symm hpgne
  -- the node of a page other than the right node's
  have hnmo : ∀ c, c ≠ rr.nv.pgid' → (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)).nm !! c = B.nm !! c := by
    intro c hcne; rw [hnm', if_neg hcne]
  have hpos' : ∀ c, c ≠ lr → ∀ x, B.nm !! x = some c → x ≠ rr.nv.pgid' := by
    intro c hcl x hx he; rw [he] at hx; exact hcl (Option.some.inj (hx.symm.trans hnmr))
  -- the parent's entries after the removal: its others
  have hmem' : ∀ x, x ∈ rp.ws.eraseIdx (k + 1) → x ∈ rp.ws ∧ x.pgid ≠ rr.nv.pgid' := by
    intro x hx
    obtain ⟨j, hji, hj⟩ := List.mem_eraseIdx_iff_getElem?.1 hx
    refine ⟨List.mem_of_getElem? hj, fun he => hji ?_⟩
    exact (honly pl rp j x hrp hbr hj (by rw [he, hpgr])).2
  have hmemw : ∀ x, x ∈ rp.ws → x.pgid ≠ rr.nv.pgid' → x ∈ rp.ws.eraseIdx (k + 1) := by
    intro x hx hne
    exact mem_eraseIdx_of_ne rp.ws (k + 1) x hx (by rw [hwr]; intro h; cases h; exact hne hpgr.symm)
  have hcs' : ∀ c, c ∈ rp.cs.eraseIdx (rp.cs.idxOf lr) ↔ c ≠ lr ∧ c ∈ rp.cs := by
    intro c; rw [cs_erase]; exact List.Nodup.mem_erase_iff hnp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- a child of `q` in the old bucket is one in the new (as `q'`)
  have hchild : ∀ (q : Loc) (l' : Loc) (x : w64), B.nm !! x = some l' → x ≠ rr.nv.pgid' →
      (∀ r', B.ns !! l' = some r' → r'.nv.parent' = q) →
      ∃ r', (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns !! l' = some r' ∧
        r'.nv.parent' = (if q = lr then ll else q) := by
    intro q l' x hx hxn hpq
    obtain ⟨-, r0, hr0, -⟩ := c5 x l' hx
    have hl'r : l' ≠ lr := by intro he; rw [he] at hx; exact hxn (hinj _ _ _ hx hnmr)
    obtain ⟨r0', h1, -, -, h4⟩ := hlook l' r0 hr0 hl'r
    exact ⟨r0', h1, by rw [h4, hpq r0 hr0]⟩
  have hmovedP : ∀ c, c ∈ kidsOf B rr.ws → ∃ rc, B.ns !! c = some rc ∧ rc.nv.parent' = lr :=
    fun c h => (hmv c).1 h
  -- the left node is a branch exactly when the right one is
  have hbrl : rr.nv.isLeaf' = false → rl.nv.isLeaf' = false := fun h => by rw [hkind]; exact h
  -- entries of either sibling, and the right node's page
  have hpgsib : ∀ x, x ∈ rl.ws ++ rr.ws → rl.nv.isLeaf' = false → x.pgid ≠ rr.nv.pgid' := by
    intro x hx hb he
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
    rcases List.mem_append.1 hx with hxl | hxr
    · obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1 hxl
      exact hllp (honly ll rl j' x hrl hb hj' (by rw [he, hpgr])).1
    · obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1 hxr
      exact hlrp (honly lr rr j' x hrr (by rw [← hkind]; exact hb) hj' (by rw [he, hpgr])).1
  refine ⟨c1, c2, fun h0 => absurd h0 hrn, fun _ => ?_, ?_, c6, fun h0 => absurd h0 hroot0, ?_, ?_, ?_⟩
  · -- the root is cached
    have h4 := c4 hrn
    show (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)).nm !! B.ib.root' = some B.bv.rootNode'
    rw [hnmo _ (hpos' _ hroot _ h4)]; exact h4
  · intro c l hl
    rw [hnm'] at hl
    split at hl
    · cases hl
    rename_i hcn
    obtain ⟨hnn, r0, hr0, hp0⟩ := c5 c l hl
    have hlr' : l ≠ lr := by intro he; rw [he] at hl; exact hcn (hinj _ _ _ hl hnmr)
    obtain ⟨r0', h1, h2, -, -⟩ := hlook l r0 hr0 hlr'
    exact ⟨hnn, r0', h1, by rw [h2]; exact hp0⟩
  · intro y ry' hy
    rw [hns'] at hy
    split at hy
    · -- the parent
      rename_i hyp
      cases hy; subst y
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := hnp
      refine ⟨n1, ?_, wsSorted_eraseIdx _ _ n3, fun x hx => n4 x (List.mem_of_mem_eraseIdx hx),
        fun x hx => n5 x (List.mem_of_mem_eraseIdx hx), n6, ?_, n8, n9, n10, fun h => ?_,
        fun _ => ?_, n13, fun hp => ?_, ?_, ?_⟩
      · show (rp.ins.eraseIdx (k + 1)).length = (rp.ws.eraseIdx (k + 1)).length
        rw [List.length_eraseIdx_of_lt (by omega), List.length_eraseIdx_of_lt hil, hilen]
      · show _ !! rp.nv.pgid' = some pl
        rw [hnmo _ (hpos' pl (Ne.symm hlrp) _ n7)]; exact n7
      · exact absurd (h.symm.trans hbr) (by nofun)
      · obtain ⟨-, -, hk⟩ := n12 hbr
        refine ⟨by show 0 < (rp.ws.eraseIdx (k + 1)).length; rw [List.length_eraseIdx_of_lt hil]; omega,
          (hnd.sublist ((List.eraseIdx_sublist _ _).map _)), fun x hx => ?_⟩
        obtain ⟨hxm, hxn⟩ := hmem' x hx
        obtain ⟨k1, k2, k3⟩ := hk x hxm
        refine ⟨k1, fun l' hl' => ?_, fun hn => ?_⟩
        · rw [hnmo _ hxn] at hl'
          obtain ⟨r', h1, h2⟩ := hchild pl l' x.pgid hl' hxn (fun r' hr' => by
            obtain ⟨r'', h1, h2⟩ := k2 l' hl'; rw [hr'] at h1; cases h1; exact h2)
          exact ⟨r', h1, by rw [h2, if_neg (Ne.symm hlrp)]⟩
        · rw [hnmo _ hxn] at hn; exact k3 hn
      · obtain ⟨rq, hrq, hbq, hiq, x, hx, hxp⟩ := n14 hp
        have hqr : rp.nv.parent' ≠ lr := fun he => hcyc pl rp hrp (Or.inr he) rfl
        have hql : rp.nv.parent' ≠ ll := fun he => hcyc pl rp hrp (Or.inl he) rfl
        show ∃ rq', (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
          (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns !! rp.nv.parent' = some rq' ∧ rq'.nv.isLeaf' = false ∧
          pl ∈ rq'.cs ∧ ∃ w, w ∈ rq'.ws ∧ w.pgid = rp.nv.pgid'
        rw [hother _ rq hrq hnself hql hqr]
        refine ⟨_, rfl, ?_, ?_, x, ?_, hxp⟩ <;> split <;> assumption
      · show (rp.cs.eraseIdx (rp.cs.idxOf lr)).Nodup
        rw [cs_erase]; exact n15.erase _
      · intro c hcin
        obtain ⟨hcn, hcm⟩ := (hcs' c).1 hcin
        obtain ⟨rc, hrc, hpc⟩ := n16 c hcm
        obtain ⟨rc', h1, -, -, h4⟩ := hlook c rc hrc hcn
        exact ⟨rc', h1, by rw [h4, hpc, if_neg (Ne.symm hlrp)]⟩
    rename_i hyp
    split at hy
    · -- the left node
      rename_i hyl
      cases hy; subst y
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := hnl
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16⟩ := hnr
      have hpdis : rl.nv.isLeaf' = false → ∀ x ∈ rl.ws, ∀ y ∈ rr.ws, x.pgid ≠ y.pgid := by
        intro hb x hx y hy he
        have hbr' : rr.nv.isLeaf' = false := by rw [← hkind]; exact hb
        obtain ⟨-, -, hkl⟩ := n12 hb
        obtain ⟨-, -, hkr⟩ := m12 hbr'
        cases hc0 : B.nm !! x.pgid with
        | some cn =>
          obtain ⟨r1, hr1, hq1⟩ := (hkl x hx).2.1 cn hc0
          obtain ⟨r2, hr2, hq2⟩ := (hkr y hy).2.1 cn (by rw [← he]; exact hc0)
          rw [hr1] at hr2; cases hr2; exact hllr (hq1.symm.trans hq2)
        | none =>
          obtain ⟨jx, hjx⟩ := List.mem_iff_getElem?.1 hx
          obtain ⟨jy, hjy⟩ := List.mem_iff_getElem?.1 hy
          have hp1' : pagePosAt B ll jx x.pgid := ⟨rl, x, hrl, hb, hjx, rfl, hc0⟩
          have hp2' : pagePosAt B lr jy x.pgid := ⟨rr, y, hrr, hbr', hjy, he.symm, hc0⟩
          have hwf := (hkl x hx).2.2 hc0
          obtain ⟨pgx, hpgx⟩ : ∃ pg, W.pages !! uint.nat x.pgid = some pg := by
            cases hwf with
            | page _ pg _ hpg _ _ => exact ⟨pg, hpg⟩
          have hself' := treeHas_self _ _ pgx hpgx
          exact c9 ll jx x.pgid lr jy x.pgid hp1' hp2' (by intro h; simp only [Prod.mk.injEq] at h; exact hllr h.1)
            _ hself' hself'
      refine ⟨n1, ?_, ?_, ?_, ?_, n6, ?_, n8, n9, n10, ?_, ?_, fun h => absurd h (by show ¬ rl.nv.parent' = null; rw [hp1]; exact hpn),
        fun _ => ?_, ?_, ?_⟩
      · show (rl.ins ++ rr.ins).length = (rl.ws ++ rr.ws).length
        rw [List.length_append, List.length_append, n2, m2]
      · show wsSorted (rl.ws ++ rr.ws)
        rw [wsSorted_iff] at n3 m3 ⊢
        exact List.pairwise_append.2 ⟨n3, m3, fun a ha b hb => hlt a ha b hb⟩
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact n4 x h
        · exact m4 x h
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact n5 x h
        · exact m5 x h
      · show _ !! rl.nv.pgid' = some ll
        rw [hnmo _ (Ne.symm hpgr')]; exact n7
      · intro hlf x hx
        rcases List.mem_append.1 hx with h | h
        · exact n11 hlf x h
        · exact m11 (by rw [← hkind]; exact hlf) x h
      · intro hb
        have hb' : rl.nv.isLeaf' = false := hb
        have hbr' : rr.nv.isLeaf' = false := by rw [← hkind]; exact hb
        obtain ⟨a1, a2, a3⟩ := n12 hb'
        obtain ⟨b1, b2, b3⟩ := m12 hbr'
        refine ⟨by show 0 < (rl.ws ++ rr.ws).length; rw [List.length_append]; omega, ?_, fun x hx => ?_⟩
        · show ((rl.ws ++ rr.ws).map WEntry.pgid).Nodup
          rw [List.map_append, List.nodup_append]
          refine ⟨a2, b2, fun a ha b hb'' he => ?_⟩
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb''
          exact hpdis hb' x hx y hy he
        · have hxn := hpgsib x hx hb'
          rcases List.mem_append.1 hx with h | h
          · obtain ⟨k1, k2, k3⟩ := a3 x h
            refine ⟨k1, fun l' hl' => ?_, fun hn => by rw [hnmo _ hxn] at hn; exact k3 hn⟩
            rw [hnmo _ hxn] at hl'
            obtain ⟨r', h1, h2⟩ := hchild ll l' x.pgid hl' hxn (fun r' hr' => by
              obtain ⟨r'', h1, h2⟩ := k2 l' hl'; rw [hr'] at h1; cases h1; exact h2)
            exact ⟨r', h1, by rw [h2, if_neg hllr]⟩
          · obtain ⟨k1, k2, k3⟩ := b3 x h
            refine ⟨k1, fun l' hl' => ?_, fun hn => by rw [hnmo _ hxn] at hn; exact k3 hn⟩
            rw [hnmo _ hxn] at hl'
            obtain ⟨r', h1, h2⟩ := hchild lr l' x.pgid hl' hxn (fun r' hr' => by
              obtain ⟨r'', h1, h2⟩ := k2 l' hl'; rw [hr'] at h1; cases h1; exact h2)
            exact ⟨r', h1, by rw [h2, if_pos rfl]⟩
      · show ∃ rq : NRec, (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
          (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns !! rl.nv.parent' = some rq ∧ rq.nv.isLeaf' = false ∧
          ll ∈ rq.cs ∧ ∃ w : WEntry, w ∈ rq.ws ∧ w.pgid = rl.nv.pgid'
        rw [hp1, hns', if_pos rfl]
        refine ⟨_, rfl, hbr, (hcs' ll).2 ⟨hllr, hinl⟩, wl, ?_, hpgl.symm⟩
        exact hmemw wl (List.mem_of_getElem? hwl) (by rw [hpgr]; exact hpgne)
      · show (rl.cs ++ kidsOf B rr.ws).Nodup
        rw [List.nodup_append]
        refine ⟨n15, hmnd, fun a ha b hb he => ?_⟩
        subst he
        obtain ⟨rc, hrc, hpc⟩ := n16 a ha
        obtain ⟨rc', hrc', hpc'⟩ := hmovedP a hb
        rw [hrc] at hrc'; cases hrc'; exact hllr (hpc.symm.trans hpc')
      · intro c hcin
        rcases List.mem_append.1 hcin with h | h
        · obtain ⟨rc, hrc, hpc⟩ := n16 c h
          have hcr : c ≠ lr := by intro he; rw [he, hrr] at hrc; cases hrc; rw [hp2] at hpc; exact hllp hpc.symm
          obtain ⟨rc', h1, -, -, h4⟩ := hlook c rc hrc hcr
          exact ⟨rc', h1, by rw [h4, hpc, if_neg hllr]⟩
        · obtain ⟨rc, hrc, hpc⟩ := hmovedP c h
          have hcr : c ≠ lr := by
            intro he; rw [he, hrr] at hrc; cases hrc; rw [hp2] at hpc; exact hlrp hpc.symm
          obtain ⟨rc', h1, -, -, h4⟩ := hlook c rc hrc hcr
          exact ⟨rc', h1, by rw [h4, hpc, if_pos rfl]⟩
    rename_i hyl
    split at hy
    · cases hy
    rename_i hyr
    -- another node
    obtain ⟨ry, hry, rfl⟩ := Option.map_eq_some_iff.1 hy
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := c8 y ry hry
    have hpgy : ry.nv.pgid' ≠ rr.nv.pgid' := hpos' y hyr _ n7
    have hgen : ∀ ry' : NRec, ry'.ws = ry.ws → ry'.cs = ry.cs → ry'.ins = ry.ins → ry'.key = ry.key →
        ry'.ksrc = ry.ksrc → ry'.nv.bucket' = ry.nv.bucket' → ry'.nv.isLeaf' = ry.nv.isLeaf' →
        ry'.nv.spilled' = ry.nv.spilled' → ry'.nv.key' = ry.nv.key' → ry'.nv.pgid' = ry.nv.pgid' →
        ry'.nv.parent' = (if ry.nv.parent' = lr then ll else ry.nv.parent') →
        nodeClean W hwm bl (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
          (mgLeft rl rr (kidsOf B rr.ws) sI sC)) y ry' := by
      intro ry' e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
      refine ⟨by rw [e6]; exact n1, by rw [e3, e1]; exact n2, by rw [e1]; exact n3,
        by rw [e1]; exact n4, by rw [e1]; exact n5, by rw [e8]; exact n6,
        by rw [e10, hnmo _ hpgy]; exact n7, by rw [e10]; exact n8, by rw [e10]; exact n9,
        by rw [e9, e4, e5]; exact n10, by rw [e7, e1]; exact n11, ?_, ?_, ?_, by rw [e2]; exact n15, ?_⟩
      · intro hb
        rw [e7] at hb; rw [e1]
        obtain ⟨a1, a2, a3⟩ := n12 hb
        refine ⟨a1, a2, fun x hx => ?_⟩
        obtain ⟨k1, k2, k3⟩ := a3 x hx
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
        have hxn : x.pgid ≠ rr.nv.pgid' := fun he => hyp (honly y ry j x hry hb hj (by rw [he, hpgr])).1
        refine ⟨k1, fun l' hl' => ?_, fun hn => by rw [hnmo _ hxn] at hn; exact k3 hn⟩
        rw [hnmo _ hxn] at hl'
        obtain ⟨r', h1, h2⟩ := hchild y l' x.pgid hl' hxn (fun r' hr' => by
          obtain ⟨r'', h1, h2⟩ := k2 l' hl'; rw [hr'] at h1; cases h1; exact h2)
        exact ⟨r', h1, by rw [h2, if_neg hyr]⟩
      · intro hp
        rw [e11] at hp
        split at hp
        · exact absurd hp (c5 _ _ hll).1
        · exact n13 hp
      · intro hp
        rw [e11]
        split
        · -- a child of the right node, now the left one's
          rename_i hpr
          obtain ⟨rq, hrq, hbq, -, x, hx, hxp⟩ := n14 (by rw [hpr]; exact (c5 _ _ hlr).1)
          rw [hpr, hrr] at hrq; cases hrq
          refine ⟨mgLeft rl rr (kidsOf B rr.ws) sI sC, by rw [hns', if_neg hllp, if_pos rfl],
            by show rl.nv.isLeaf' = false; rw [hkind]; exact hbq,
            List.mem_append.2 (Or.inr ((hmv y).2 ⟨ry, hry, hpr⟩)), x, List.mem_append.2 (Or.inr hx),
            by rw [e10]; exact hxp⟩
        · rename_i hpr
          have hp' : ry.nv.parent' ≠ null := by rw [e11, if_neg hpr] at hp; exact hp
          obtain ⟨rq, hrq, hbq, hiq, x, hx, hxp⟩ := n14 hp'
          by_cases hqp : ry.nv.parent' = pl
          · rw [hqp, hrp] at hrq; cases hrq
            refine ⟨rmParent rp (k + 1) lr sI' sC', by rw [hqp, hns', if_pos rfl], hbq, (hcs' y).2 ⟨hyr, hiq⟩, x,
              hmemw x hx (by rw [hxp]; exact hpgy), by rw [e10]; exact hxp⟩
          by_cases hql : ry.nv.parent' = ll
          · rw [hql, hrl] at hrq; cases hrq
            refine ⟨mgLeft rl rr (kidsOf B rr.ws) sI sC, by rw [hql, hns', if_neg hllp, if_pos rfl], hbq,
              List.mem_append.2 (Or.inl hiq), x, List.mem_append.2 (Or.inl hx), by rw [e10]; exact hxp⟩
          · rw [hother _ rq hrq hqp hql hpr]
            refine ⟨_, rfl, ?_, ?_, x, ?_, by rw [e10]; exact hxp⟩ <;> split <;> assumption
      · intro c hcin
        rw [e2] at hcin
        obtain ⟨rc, hrc, hpc⟩ := n16 c hcin
        have hcr : c ≠ lr := by
          intro he; rw [he, hrr] at hrc; cases hrc; rw [hp2] at hpc; exact hyp hpc.symm
        obtain ⟨rc', h1, -, -, h4⟩ := hlook c rc hrc hcr
        exact ⟨rc', h1, by rw [h4, hpc, if_neg hyr]⟩
    split
    · exact hgen _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by rw [if_pos ‹_›])
    · exact hgen _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by rw [if_neg ‹_›])
  · intro l1 i1 q1 l2 i2 q2 h1 h2' hne d hd
    obtain ⟨n1, p1'⟩ := mg_pos W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr sI sC sI' sC' hkind l1 i1 q1 h1
    obtain ⟨n2, p2'⟩ := mg_pos W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr sI sC sI' sC' hkind l2 i2 q2 h2'
    refine c9 _ _ q1 _ _ q2 p1' p2' ?_ d hd
    intro he; apply hne
    exact mgPos_inj pl ll lr k rl.ws.length hllp hlrp hllr l1 l2 i1 i2 n1 n2
      (Prod.ext (Prod.mk.inj he).1 (Prod.mk.inj he).2)
  · intro l j q hp d hd
    obtain ⟨-, p'⟩ := mg_pos W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr sI sC sI' sC' hkind l j q hp
    rw [hnm']; split
    · rfl
    · exact c10 _ _ q p' d hd

theorem mg_keys (sI sC sI' sC' : GoSlice) (hkind : rl.nv.isLeaf' = rr.nv.isLeaf')
    (hleaf0 : rr.nv.isLeaf' = true → ∀ w ∈ rr.ws, B.nm !! w.pgid = none)
    (hroot : B.bv.rootNode' ≠ lr) (hht : rblHt W B)
    (bnd : Loc → Option (List w8) × Option (List w8)) (dfc : Option Loc)
    (hk : rblKeysB W B bnd dfc) (hdfc : dfc = some ll ∨ dfc = some lr)
    (hne : 0 < (rl.ws ++ rr.ws).length) :
    rblKeysB W (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)) (mgBnd bnd pl ll rp rl k) (some pl) := by
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, hpgl, hpgr, hnmp, hnd, hroot0, hinl, hinr, hself, hpgne, hnself⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  obtain ⟨hmv, hmnd⟩ := mg_moved W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr
    hrl hrr hleaf0
  have hcyc := mg_cyc W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have honly := mg_only W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have hlook := mg_look W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
    sI sC sI' sC'
  have hother := mg_other W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
    sI sC sI' sC'
  have hlt := mg_lt W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr bnd dfc hk
  obtain ⟨hbl, hbr'⟩ := mg_bnds W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr
    hrl hrr bnd dfc hk
  obtain ⟨e1, e2⟩ := entryBnd_mid (bnd pl) rp.ws k wr hwr
  have hnm' := mg_nm B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
    (mgLeft rl rr (kidsOf B rr.ws) sI sC)
  have hns' := mg_ns B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
    (mgLeft rl rr (kidsOf B rr.ws) sI sC)
  have hinj := nm_inj W hwm bl B hc
  have hnmr : B.nm !! rr.nv.pgid' = some lr := by rw [hpgr]; exact hlr
  have hnmo : ∀ c, c ≠ rr.nv.pgid' → (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)).nm !! c = B.nm !! c := by
    intro c hcne; rw [hnm', if_neg hcne]
  have hil : k + 1 < rp.ws.length := (List.getElem?_eq_some_iff.1 hwr).1
  obtain ⟨k1, k2, k3⟩ := hk
  obtain ⟨ht, pht, hpht, hhh⟩ := hht
  have hkid := kidLeaf W hwm bl B hc ht pht hpht hhh
  have hhl : ht ll + 1 = ht pl := ((hhh pl rp hrp).2 hbr wl (List.mem_of_getElem? hwl)).1 ll hll
  have hhr : ht lr + 1 = ht pl := ((hhh pl rp hrp).2 hbr wr (List.mem_of_getElem? hwr)).1 lr hlr
  have hbne : ∀ x, x ≠ ll → mgBnd bnd pl ll rp rl k x = bnd x := by
    intro x hx; simp [mgBnd, hx]
  have hbll : mgBnd bnd pl ll rp rl k ll = ((if rl.nv.isLeaf' then (entryBnd (bnd pl) rp.ws k).1 else
      (bnd ll).1), (entryBnd (bnd pl) rp.ws (k + 1)).2) := by simp [mgBnd]
  obtain ⟨p1, p2, p3, -, -⟩ := k3 pl rp hrp
  obtain ⟨-, pfst, kindp, pkd⟩ := p3 hbr
  have hsorted : wsSorted rp.ws := (hc.2.2.2.2.2.2.2.1 pl rp hrp).2.2.1
  -- the parent's new entry bounds
  have hposk : entryBnd (bnd pl) (rp.ws.eraseIdx (k + 1)) k =
      ((entryBnd (bnd pl) rp.ws k).1, (entryBnd (bnd pl) rp.ws (k + 1)).2) := by
    have hlen : (rp.ws.eraseIdx (k + 1)).length = rp.ws.length - 1 := List.length_eraseIdx_of_lt hil
    have hwk : ∀ j, wKey (rp.ws.eraseIdx (k + 1)) j = wKey rp.ws (if j < k + 1 then j else j + 1) := by
      intro j; unfold wKey; rw [getElem?_eraseIdx']
    unfold entryBnd childLo childHi
    rw [hlen]
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · split
      · rfl
      · rw [hwk, if_pos (by omega)]
    · by_cases h : k + 1 < rp.ws.length - 1
      · rw [if_pos h, if_pos (by omega), hwk, if_neg (by omega)]
      · rw [if_neg h, if_neg (by omega)]
  have hwrlo : ∀ y, (entryBnd (bnd pl) rp.ws k).1 = some y → ¬ go.GoStringLt wr.key y := by
    intro y hy
    have h0 := p1 wr (List.mem_of_getElem? hwr)
    unfold entryBnd childLo at hy
    simp only at hy
    split at hy
    · exact h0.1 y hy
    · cases hy
      have := hsorted k (k + 1) (by omega) hil
      have hk1 : wKey rp.ws (k + 1) = wr.key := by unfold wKey; rw [hwr]; rfl
      rw [hk1] at this; exact rk_le_of_lt this
  have hwrhi : ∀ y, (entryBnd (bnd pl) rp.ws (k + 1)).2 = some y → go.GoStringLt wr.key y := by
    intro y hy
    have h0 := p1 wr (List.mem_of_getElem? hwr)
    unfold entryBnd childHi at hy
    simp only at hy
    split at hy
    · cases hy
      rename_i h
      have := hsorted (k + 1) (k + 1 + 1) (by omega) h
      have hk1 : wKey rp.ws (k + 1) = wr.key := by unfold wKey; rw [hwr]; rfl
      rw [hk1] at this; exact this
    · exact h0.2 y hy
  obtain ⟨l1, l2, l3, l4, l5⟩ := k3 ll rl hrl
  obtain ⟨r1, r2, r3, r4, r5⟩ := k3 lr rr hrr
  have hdl : ∀ y, y ≠ ll → y ≠ lr → dfc ≠ some y := by
    intro y h1 h2 he; rcases hdfc with h | h <;> rw [h] at he <;> cases he
    · exact h1 rfl
    · exact h2 rfl
  have hrlne : rl.nv.isLeaf' = false → 0 < rl.ws.length :=
    fun hb => ((hc.2.2.2.2.2.2.2.1 ll rl hrl).2.2.2.2.2.2.2.2.2.2.2.1 hb).1
  have hrrne : rr.nv.isLeaf' = false → 0 < rr.ws.length :=
    fun hb => ((hc.2.2.2.2.2.2.2.1 lr rr hrr).2.2.2.2.2.2.2.2.2.2.2.1 hb).1
  -- the bounds of the entries of the merged node (a branch)
  have hR0 : rr.nv.isLeaf' = false → ∀ y, wKey rr.ws 0 = y → rr.ws ≠ [] →
      ∃ x, (bnd ll).2 = some x ∧ ¬ go.GoStringLt y x := by
    intro hb y hy _
    obtain ⟨xh, hxh, hxh'⟩ := hbl.2 _ e1
    refine ⟨xh, hxh, ?_⟩
    have hr0 : rr.ws[0]? = some (rr.ws[0]'(hrrne hb)) := List.getElem?_eq_getElem _
    have ky := r1 _ (List.mem_of_getElem? hr0)
    obtain ⟨yl, hyl, hyl'⟩ := hbr'.1 _ e2
    have : wKey rr.ws 0 = (rr.ws[0]'(hrrne hb)).key := by unfold wKey; rw [hr0]; rfl
    rw [← hy, this]
    exact rk_le_trans hxh' (rk_le_trans hyl' (ky.1 yl hyl))
  have hhiL : ∀ y, (entryBnd (bnd pl) rp.ws (k + 1)).2 = some y → ∃ x, (bnd ll).2 = some x ∧
      ¬ go.GoStringLt y x := by
    intro y hy
    obtain ⟨xh, hxh, hxh'⟩ := hbl.2 _ e1
    exact ⟨xh, hxh, rk_le_of_lt (rk_lt_of_le_lt hxh' (hwrhi y hy))⟩
  have hloR : rr.nv.isLeaf' = false → ∃ x, (bnd lr).1 = some x ∧ ¬ go.GoStringLt x (wKey rr.ws 0) := by
    intro hb
    obtain ⟨yl, hyl, -⟩ := hbr'.1 _ e2
    exact ⟨yl, hyl, by rw [((r3 hb).2.1 yl hyl)]; exact rk_le_refl _⟩
  have hentL : rl.nv.isLeaf' = false → ∀ j, j < rl.ws.length →
      bndIn (entryBnd (bnd ll) rl.ws j) (entryBnd (mgBnd bnd pl ll rp rl k ll) (rl.ws ++ rr.ws) j) := by
    intro hb j hj
    rw [hbll, if_neg (by rw [hb]; nofun)]
    exact entryBnd_left (bnd ll) _ rl.ws rr.ws j hj rfl (hR0 (by rw [← hkind]; exact hb)) hhiL
  have hentR : rl.nv.isLeaf' = false → ∀ j, j < rr.ws.length →
      bndIn (entryBnd (bnd lr) rr.ws j)
        (entryBnd (mgBnd bnd pl ll rp rl k ll) (rl.ws ++ rr.ws) (rl.ws.length + j)) := by
    intro hb j hj
    rw [hbll]
    exact entryBnd_right (bnd lr) _ rl.ws rr.ws j hj (hrlne hb) (hloR (by rw [← hkind]; exact hb))
      hbr'.2
  -- the entries of the parent after the removal of the right one's
  have hback : ∀ j x, (rp.ws.eraseIdx (k + 1))[j]? = some x →
      ∃ j', rp.ws[j']? = some x ∧ j' ≠ k + 1 ∧ j = (if j' < k + 1 then j' else j' - 1) := by
    intro j x hx
    rw [getElem?_eraseIdx'] at hx
    by_cases h : j < k + 1
    · rw [if_pos h] at hx; exact ⟨j, hx, by omega, by rw [if_pos h]⟩
    · rw [if_neg h] at hx; exact ⟨j + 1, hx, by omega, by rw [if_neg (by omega)]; omega⟩
  have hpos : ∀ j' x, rp.ws[j']? = some x → j' ≠ k + 1 →
      (rp.ws.eraseIdx (k + 1))[if j' < k + 1 then j' else j' - 1]? = some x := by
    intro j' x hx hji
    rw [getElem?_eraseIdx']
    have : (if (if j' < k + 1 then j' else j' - 1) < k + 1 then (if j' < k + 1 then j' else j' - 1)
        else (if j' < k + 1 then j' else j' - 1) + 1) = j' := by
      by_cases h : j' < k + 1
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg (by omega)]; omega
    rw [this]; exact hx
  have hentP : ∀ j', j' < rp.ws.length → j' ≠ k + 1 →
      bndIn (entryBnd (bnd pl) rp.ws j')
        (entryBnd (bnd pl) (rp.ws.eraseIdx (k + 1)) (if j' < k + 1 then j' else j' - 1)) := by
    intro j' hj' hji
    have := entryBnd_erase rp.ws (k + 1) (bnd pl) hsorted p1 (by omega) hil j' hj' hji
    rwa [if_neg (by omega)] at this
  -- a child in the old bucket, its record in the new
  have hkidrec : ∀ (q : Loc) (x : WEntry) (l' : Loc), B.nm !! x.pgid = some l' → x.pgid ≠ rr.nv.pgid' →
      ∀ r0, B.ns !! l' = some r0 → ∃ r', (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns !! l' = some r' ∧ r'.nv.isLeaf' = r0.nv.isLeaf' := by
    intro q x l' hl' hxn r0 hr0
    have hl'r : l' ≠ lr := by intro he; rw [he] at hl'; exact hxn (hinj _ _ _ hl' hnmr)
    obtain ⟨r', h1, -, h3, -⟩ := hlook l' r0 hr0 hl'r
    exact ⟨r', h1, h3⟩
  refine ⟨k1, fun r0 h0 => ?_, fun y ry' hy => ?_⟩
  · -- the root
    change (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns !! B.bv.rootNode' = some r0 at h0
    rw [hns'] at h0
    split at h0
    · rename_i he; cases h0; exact k2 rp (by rw [he]; exact hrp)
    split at h0
    · rename_i _ he; cases h0
      have := k2 rl (by rw [he]; exact hrl); rw [hp1] at this; exact absurd this hpn
    obtain ⟨r1', hr1', rfl⟩ := Option.map_eq_some_iff.1 h0
    have := k2 r1' hr1'
    rw [if_neg (by rw [this]; intro h; rw [← h] at hlr; exact (hc.2.2.2.2.1 _ _ hlr).1 rfl)]
    exact this
  rw [hns'] at hy
  split at hy
  · -- the parent
    rename_i hyp
    cases hy; subst y
    refine ⟨fun x hx => by rw [hbne _ (Ne.symm hllp)]; exact p1 x (List.mem_of_mem_eraseIdx hx),
      fun hp => ?_, fun _ => ⟨fun h => absurd rfl h, fun x hx => ?_, kindp, ?_⟩,
      fun h => absurd rfl h, fun h => absurd h (by show ¬ (rp.nv.isLeaf' = true); rw [hbr]; nofun)⟩
    · obtain ⟨hkey, rq, i, x, hrq, hx, hxp, hxk, hbn⟩ := p2 hp
      have hqr : rp.nv.parent' ≠ lr := fun he => hcyc pl rp hrp (Or.inr he) rfl
      have hql : rp.nv.parent' ≠ ll := fun he => hcyc pl rp hrp (Or.inl he) rfl
      refine ⟨hkey, _, i, x, hother _ rq hrq hnself hql hqr, ?_, hxp, hxk, ?_⟩
      · split <;> exact hx
      · show bndIn (mgBnd bnd pl ll rp rl k pl) (entryBnd (mgBnd bnd pl ll rp rl k rp.nv.parent') _ i)
        rw [hbne _ (Ne.symm hllp), hbne _ hql]
        split <;> exact hbn
    · rw [hbne _ (Ne.symm hllp)] at hx
      show wKey (rp.ws.eraseIdx (k + 1)) 0 = x
      unfold wKey; rw [getElem?_eraseIdx', if_pos (by omega)]
      exact pfst x hx
    · intro j x hx
      obtain ⟨j', hj', hji, rfl⟩ := hback j x hx
      have hxn : x.pgid ≠ rr.nv.pgid' := by
        intro he; exact hji (honly pl rp j' x hrp hbr hj' (by rw [he, hpgr])).2
      obtain ⟨a1, a2⟩ := pkd j' x hj'
      refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
      · rw [hnmo _ hxn] at hl'
        obtain ⟨r0, hr0, hk0⟩ := a1 l' hl'
        obtain ⟨r', h1, h2⟩ := hkidrec pl x l' hl' hxn r0 hr0
        exact ⟨r', h1, by rw [h2]; exact hk0⟩
      · rw [hnmo _ hxn] at hn
        obtain ⟨pg, b1, b2, b3, b4, b5⟩ := a2 hn
        refine ⟨pg, b1, b2, b3, b4, ?_⟩
        rw [hbne _ (Ne.symm hllp)]
        exact treeKeys_mono W.pages _ _ _ b5 _ _
          (hentP j' (List.getElem?_eq_some_iff.1 hj').1 hji)
  rename_i hyp
  split at hy
  · -- the merged node
    rename_i hyl
    cases hy; subst y
    have hlo0 : ∀ x ∈ rl.ws ++ rr.ws, keyGe (mgBnd bnd pl ll rp rl k ll).1 x.key := by
      intro x hx y hy
      rw [hbll] at hy
      simp only at hy
      rcases List.mem_append.1 hx with h | h
      · have kx := keyIn_bndIn hbl _ (l1 x h)
        split at hy
        · exact kx.1 y hy
        · exact (l1 x h).1 y hy
      · have ky := keyIn_bndIn hbr' _ (r1 x h)
        have hwx : ¬ go.GoStringLt x.key wr.key := ky.1 wr.key e2
        split at hy
        · exact rk_le_trans (hwrlo y hy) hwx
        · rename_i hb
          have hb' : rl.nv.isLeaf' = false := by simpa using hb
          have hr0 : rl.ws[0]? = some (rl.ws[0]'(hrlne hb')) := List.getElem?_eq_getElem _
          have hy0 := (l3 hb').2.1 y hy
          have : wKey rl.ws 0 = (rl.ws[0]'(hrlne hb')).key := by unfold wKey; rw [hr0]; rfl
          rw [this] at hy0; rw [← hy0]
          exact rk_le_of_lt (hlt _ (List.mem_of_getElem? hr0) x h)
    have hhi0 : ∀ x ∈ rl.ws ++ rr.ws, keyLt x.key (mgBnd bnd pl ll rp rl k ll).2 := by
      intro x hx y hy
      rw [hbll] at hy
      simp only at hy
      rcases List.mem_append.1 hx with h | h
      · have kx := keyIn_bndIn hbl _ (l1 x h)
        exact goStringLt_trans (kx.2 _ e1) (hwrhi y hy)
      · exact (keyIn_bndIn hbr' _ (r1 x h)).2 y hy
    refine ⟨fun x hx => ⟨hlo0 x hx, hhi0 x hx⟩, fun hp => ?_, fun hb => ?_, fun _ hlf hu hp => ?_,
      fun hlf x hx => ?_⟩
    · -- its position: the left one's entry, the right one's high bound
      obtain ⟨hkey, rq, i, x, hrq, hx, hxp, hxk, -⟩ := l2 (by rw [hp1]; exact hpn)
      rw [hp1, hrp] at hrq; cases hrq
      have hik : i = k := by
        by_cases h : i = k
        · exact h
        · exact absurd (by rw [hxp, hpgl]) (nodup_pgid_ne rp.ws hnd k i wl x hwl hx h)
      subst hik
      refine ⟨hkey, rmParent rp (i + 1) lr sI' sC', i, x, by change _ !! rl.nv.parent' = _; rw [hp1, hns', if_pos rfl], ?_, hxp, hxk, ?_⟩
      · show (rp.ws.eraseIdx (i + 1))[i]? = some x
        rw [getElem?_eraseIdx', if_pos (by omega)]; exact hx
      · show bndIn (mgBnd bnd pl ll rp rl i ll)
          (entryBnd (mgBnd bnd pl ll rp rl i rl.nv.parent') (rp.ws.eraseIdx (i + 1)) i)
        rw [hp1, hbne _ (Ne.symm hllp), hposk, hbll]
        refine ⟨fun y hy => ?_, fun y hy => ⟨y, hy, rk_le_refl y⟩⟩
        split
        · exact ⟨y, hy, rk_le_refl y⟩
        · exact hbl.1 y hy
    · -- a branch
      have hb' : rl.nv.isLeaf' = false := hb
      have hbr2 : rr.nv.isLeaf' = false := by rw [← hkind]; exact hb'
      refine ⟨fun _ => ?_, fun x hx => ?_, decide (ht ll = 1), fun j x hx => ?_⟩
      · show 2 ≤ (rl.ws ++ rr.ws).length
        rw [List.length_append]; have := hrlne hb'; have := hrrne hbr2; omega
      · rw [hbll, if_neg (by rw [hb']; nofun)] at hx
        show wKey (rl.ws ++ rr.ws) 0 = x
        rw [wKey_append_left _ _ 0 (hrlne hb')]; exact (l3 hb').2.1 x hx
      · have hx' : (rl.ws ++ rr.ws)[j]? = some x := hx
        by_cases hj : j < rl.ws.length
        · rw [List.getElem?_append_left hj] at hx'
          have hxn : x.pgid ≠ rr.nv.pgid' := by
            intro he; exact hllp (honly ll rl j x hrl hb' hx' (by rw [he, hpgr])).1
          obtain ⟨a1, a2⟩ := ((l3 hb').2.2.choose_spec) j x hx'
          have hkd := hkid ll rl hrl hb' x (List.mem_of_getElem? hx')
          refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
          · rw [hnmo _ hxn] at hl'
            obtain ⟨-, r0, hr0, -⟩ := hc.2.2.2.2.1 _ _ hl'
            obtain ⟨r', h1, h2⟩ := hkidrec ll x l' hl' hxn r0 hr0
            exact ⟨r', h1, by rw [h2]; exact hkd.1 l' r0 hl' hr0⟩
          · rw [hnmo _ hxn] at hn
            obtain ⟨pg, b1, b2, b3, b4, b5⟩ := a2 hn
            refine ⟨pg, b1, b2, by rw [hkd.2 hn pg b1 b2], b4, ?_⟩
            exact treeKeys_mono W.pages _ _ _ b5 _ _ (hentL hb' j hj)
        · obtain ⟨j', rfl⟩ : ∃ j', j = rl.ws.length + j' := ⟨j - rl.ws.length, by omega⟩
          rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at hx'
          have hxn : x.pgid ≠ rr.nv.pgid' := by
            intro he
            have := honly lr rr j' x hrr hbr2 hx' (by rw [he, hpgr])
            exact hlrp this.1
          obtain ⟨a1, a2⟩ := ((r3 hbr2).2.2.choose_spec) j' x hx'
          have hkd := hkid lr rr hrr hbr2 x (List.mem_of_getElem? hx')
          have hht' : decide (ht lr = 1) = decide (ht ll = 1) := by
            congr 1; apply propext; omega
          refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
          · rw [hnmo _ hxn] at hl'
            obtain ⟨-, r0, hr0, -⟩ := hc.2.2.2.2.1 _ _ hl'
            obtain ⟨r', h1, h2⟩ := hkidrec ll x l' hl' hxn r0 hr0
            exact ⟨r', h1, by rw [h2, ← hht']; exact hkd.1 l' r0 hl' hr0⟩
          · rw [hnmo _ hxn] at hn
            obtain ⟨pg, b1, b2, b3, b4, b5⟩ := a2 hn
            refine ⟨pg, b1, b2, by rw [hkd.2 hn pg b1 b2, hht'], b4, ?_⟩
            exact treeKeys_mono W.pages _ _ _ b5 _ _
              (hentR hb' j' (List.getElem?_eq_some_iff.1 hx').1)
    · exact hne
    · rcases List.mem_append.1 hx with h | h
      · exact l5 hlf x h
      · exact r5 (by rw [← hkind]; exact hlf) x h
  rename_i hyl
  split at hy
  · cases hy
  rename_i hyr
  -- another node
  obtain ⟨ry, hry, rfl⟩ := Option.map_eq_some_iff.1 hy
  obtain ⟨n1, n2, n3, n4, n5⟩ := k3 y ry hry
  have hnc := hc.2.2.2.2.2.2.2.1 y ry hry
  have hpgy : ry.nv.pgid' ≠ rr.nv.pgid' := by
    intro he; have h7 := hnc.2.2.2.2.2.2.1; rw [he] at h7; exact hyr (Option.some.inj (h7.symm.trans hnmr))
  have hgen : ∀ ry' : NRec, ry'.ws = ry.ws → ry'.key = ry.key → ry'.nv.isLeaf' = ry.nv.isLeaf' →
      ry'.nv.key' = ry.nv.key' → ry'.nv.pgid' = ry.nv.pgid' → ry'.nv.unbalanced' = ry.nv.unbalanced' →
      ry'.nv.parent' = (if ry.nv.parent' = lr then ll else ry.nv.parent') →
      rblNodeKeys W (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)) (mgBnd bnd pl ll rp rl k) (some pl) y ry' := by
    intro ry' e1 e2 e3 e4 e5 e6 e7
    refine ⟨by rw [e1, hbne _ hyl]; exact n1, fun hp => ?_, fun hb => ?_, fun hd hlf hu hp => ?_,
      by rw [e3, e1]; exact n5⟩
    · rw [e7] at hp
      have hp0 : ry.nv.parent' ≠ null := by
        split at hp
        · rename_i h; rw [h]; exact (hc.2.2.2.2.1 _ _ hlr).1
        · exact hp
      obtain ⟨hkey, rq, i, x, hrq, hx, hxp, hxk, hbn⟩ := n2 hp0
      refine ⟨by rw [e4]; exact hkey, ?_⟩
      rw [e7, e5, e2, hbne _ hyl]
      by_cases hpr : ry.nv.parent' = lr
      · -- a child of the right node: now the left one's, at the right one's place
        rw [if_pos hpr]
        rw [hpr, hrr] at hrq; cases hrq
        have hbr2 : rr.nv.isLeaf' = false := by
          obtain ⟨rq', hrq', hbq, -⟩ := hnc.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp0
          rw [hpr, hrr] at hrq'; cases hrq'; exact hbq
        refine ⟨mgLeft rl rr (kidsOf B rr.ws) sI sC, rl.ws.length + i, x, by rw [hns', if_neg hllp, if_pos rfl], ?_,
          hxp, hxk, ?_⟩
        · show (rl.ws ++ rr.ws)[rl.ws.length + i]? = some x
          rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hx
        · rw [hpr] at hbn
          exact bndIn_trans hbn (hentR (by rw [hkind]; exact hbr2) i (List.getElem?_eq_some_iff.1 hx).1)
      · rw [if_neg hpr]
        by_cases hqp : ry.nv.parent' = pl
        · rw [hqp, hrp] at hrq; cases hrq
          have hji : i ≠ k + 1 := by
            intro he; subst he; rw [hwr] at hx; cases hx; exact hpgy (by rw [← hxp, hpgr])
          refine ⟨rmParent rp (k + 1) lr sI' sC', if i < k + 1 then i else i - 1, x,
            by rw [hqp, hns', if_pos rfl], hpos i x hx hji, hxp, hxk, ?_⟩
          rw [hqp, hbne _ (Ne.symm hllp)]
          rw [hqp] at hbn
          exact bndIn_trans hbn (hentP i (List.getElem?_eq_some_iff.1 hx).1 hji)
        by_cases hql : ry.nv.parent' = ll
        · rw [hql, hrl] at hrq; cases hrq
          have hbl2 : rl.nv.isLeaf' = false := by
            obtain ⟨rq', hrq', hbq, -⟩ := hnc.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp0
            rw [hql, hrl] at hrq'; cases hrq'; exact hbq
          refine ⟨mgLeft rl rr (kidsOf B rr.ws) sI sC, i, x, by rw [hql, hns', if_neg hllp, if_pos rfl], ?_,
            hxp, hxk, ?_⟩
          · show (rl.ws ++ rr.ws)[i]? = some x
            rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1]; exact hx
          · rw [hql] at hbn ⊢
            exact bndIn_trans hbn (hentL hbl2 i (List.getElem?_eq_some_iff.1 hx).1)
        · refine ⟨_, i, x, hother _ rq hrq hqp hql hpr, ?_, hxp, hxk, ?_⟩
          · split <;> exact hx
          · rw [hbne _ hql]; split <;> exact hbn
    · rw [e3] at hb
      obtain ⟨a1, a2, kind, a3⟩ := n3 hb
      refine ⟨fun _ => by rw [e1]; exact a1 (hdl y hyl hyr), by rw [e1, hbne _ hyl]; exact a2, kind,
        fun j x hx => ?_⟩
      rw [e1] at hx
      obtain ⟨b1, b2⟩ := a3 j x hx
      have hxn : x.pgid ≠ rr.nv.pgid' := fun he => hyp (honly y ry j x hry hb hx (by rw [he, hpgr])).1
      refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
      · rw [hnmo _ hxn] at hl'
        obtain ⟨r0, hr0, hk0⟩ := b1 l' hl'
        obtain ⟨r', h1, h2⟩ := hkidrec y x l' hl' hxn r0 hr0
        exact ⟨r', h1, by rw [h2]; exact hk0⟩
      · rw [hnmo _ hxn] at hn
        rw [hbne _ hyl, e1]; exact b2 hn
    · rw [e3] at hlf; rw [e6] at hu; rw [e1]
      have hp0 : ry.nv.parent' ≠ null := by
        rw [e7] at hp; split at hp
        · rename_i h; rw [h]; exact (hc.2.2.2.2.1 _ _ hlr).1
        · exact hp
      exact n4 (hdl y hyl hyr) hlf hu hp0
  split
  · exact hgen _ rfl rfl rfl rfl rfl rfl (by rw [if_pos ‹_›])
  · exact hgen _ rfl rfl rfl rfl rfl rfl (by rw [if_neg ‹_›])

theorem mg_acyc (sI sC sI' sC' : GoSlice) :
    rblAcyc (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)) := by
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, -, -, -, -, -, -, -, hself, -, hnself⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have hcyc := mg_cyc W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  obtain ⟨ht, hh⟩ := ha
  have h1 := hh ll rl hrl (by rw [hp1]; exact hpn)
  have h2 := hh lr rr hrr (by rw [hp2]; exact hpn)
  rw [hp1] at h1; rw [hp2] at h2
  refine ⟨fun x => if x = ll then max (ht ll) (ht lr) else ht x, fun y ry' hy hp => ?_⟩
  rw [mg_ns] at hy
  split at hy
  · rename_i hyp; cases hy; subst y
    have hq := hh pl rp hrp hp
    have hql : rp.nv.parent' ≠ ll := fun he => hcyc pl rp hrp (Or.inl he) rfl
    show (if pl = ll then _ else ht pl) < (if rp.nv.parent' = ll then _ else ht rp.nv.parent')
    rw [if_neg (Ne.symm hllp), if_neg hql]; exact hq
  split at hy
  · rename_i _ hyl; cases hy; subst y
    show (if ll = ll then max (ht ll) (ht lr) else ht ll) < (if rl.nv.parent' = ll then _ else ht rl.nv.parent')
    rw [if_pos rfl, hp1, if_neg (Ne.symm hllp)]; omega
  split at hy
  · cases hy
  rename_i hyp hyl hyr
  obtain ⟨ry, hry, rfl⟩ := Option.map_eq_some_iff.1 hy
  show (if y = ll then _ else ht y) < _
  rw [if_neg hyl]
  by_cases hpr : ry.nv.parent' = lr
  · simp only [if_pos hpr] at hp ⊢
    have := hh y ry hry (by rw [hpr]; exact (hc.2.2.2.2.1 _ _ hlr).1)
    rw [hpr] at this; simp only [↓reduceIte]; omega
  · simp only [if_neg hpr] at hp ⊢
    have := hh y ry hry hp
    split
    · rename_i he; rw [he] at this; omega
    · exact this

theorem mg_ht (sI sC sI' sC' : GoSlice) (hkind : rl.nv.isLeaf' = rr.nv.isLeaf') (hht : rblHt W B) :
    rblHt W (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)) := by
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, hpgl, hpgr, -⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have honly := mg_only W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  obtain ⟨ht, pht, hp, hh⟩ := hht
  have hhl : ht ll + 1 = ht pl := ((hh pl rp hrp).2 hbr wl (List.mem_of_getElem? hwl)).1 ll hll
  have hhr : ht lr + 1 = ht pl := ((hh pl rp hrp).2 hbr wr (List.mem_of_getElem? hwr)).1 lr hlr
  have hnm' := mg_nm B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
    (mgLeft rl rr (kidsOf B rr.ws) sI sC)
  have hent : ∀ y ry, B.ns !! y = some ry → ry.nv.isLeaf' = false → ∀ x ∈ ry.ws, x.pgid ≠ rr.nv.pgid' →
      (∀ l', (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)).nm !! x.pgid = some l' → ht l' + 1 = ht y) ∧
      ((mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)).nm !! x.pgid = none → pht (uint.nat x.pgid) + 1 = ht y) := by
    intro y ry hy hb x hx hxn
    rw [hnm', if_neg hxn]
    exact (hh y ry hy).2 hb x hx
  refine ⟨ht, pht, hp, fun y ry' hy => ?_⟩
  rw [mg_ns] at hy
  split at hy
  · rename_i hyp; cases hy; subst y
    refine ⟨fun h => absurd h (by show ¬ (rp.nv.isLeaf' = true); rw [hbr]; nofun), fun _ x hx => ?_⟩
    obtain ⟨j, hji, hj⟩ := List.mem_eraseIdx_iff_getElem?.1 hx
    exact hent pl rp hrp hbr x (List.mem_of_getElem? hj)
      (fun he => hji (honly pl rp j x hrp hbr hj (by rw [he, hpgr])).2)
  split at hy
  · rename_i _ hyl; cases hy; subst y
    refine ⟨fun h => (hh ll rl hrl).1 h, fun hb x hx => ?_⟩
    have hb' : rl.nv.isLeaf' = false := hb
    have hbr2 : rr.nv.isLeaf' = false := by rw [← hkind]; exact hb'
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
      exact hent ll rl hrl hb' x h (fun he => hllp (honly ll rl j x hrl hb' hj (by rw [he, hpgr])).1)
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
      obtain ⟨a1, a2⟩ := hent lr rr hrr hbr2 x h (fun he => hlrp (honly lr rr j x hrr hbr2 hj (by rw [he, hpgr])).1)
      exact ⟨fun l' hl' => by have := a1 l' hl'; omega, fun hn => by have := a2 hn; omega⟩
  split at hy
  · cases hy
  rename_i hyp hyl hyr
  obtain ⟨ry, hry, rfl⟩ := Option.map_eq_some_iff.1 hy
  have key : ((if ry.nv.parent' = lr then ({ ry with nv := { ry.nv with parent' := ll } } : NRec) else ry).nv.isLeaf' = ry.nv.isLeaf') ∧
      ((if ry.nv.parent' = lr then ({ ry with nv := { ry.nv with parent' := ll } } : NRec) else ry).ws = ry.ws) := by
    split <;> exact ⟨rfl, rfl⟩
  rw [key.1, key.2]
  refine ⟨(hh y ry hry).1, fun hb x hx => ?_⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
  exact hent y ry hry hb x hx (fun he => hyp (honly y ry j x hry hb hj (by rw [he, hpgr])).1)

theorem mg_unbal (sI sC sI' sC' : GoSlice) (y : Loc) (ry' : NRec)
    (hy : (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns !! y = some ry') (hu : ry'.nv.unbalanced' = true) :
    y = pl ∨ (y ≠ lr ∧ ∃ ry, B.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧ ry'.nv.pgid' = ry.nv.pgid') := by
  obtain ⟨hp1, hp2, hllr, -⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  rw [mg_ns] at hy
  split at hy
  · rename_i h; exact Or.inl h
  split at hy
  · rename_i _ hyl; cases hy; subst y
    exact Or.inr ⟨hllr, rl, hrl, hu, rfl⟩
  split at hy
  · cases hy
  rename_i _ _ hyr
  obtain ⟨ry, hry, rfl⟩ := Option.map_eq_some_iff.1 hy
  refine Or.inr ⟨hyr, ry, hry, ?_, ?_⟩ <;> split at hu <;> first | exact hu | (split <;> rfl)

theorem mg_entryIn (sI sC sI' sC' : GoSlice) (hkind : rl.nv.isLeaf' = rr.nv.isLeaf') (kk v : List w8)
    (h : entryIn W B kk v) :
    entryIn W (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)) kk v := by
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, hpgl, hpgr, -⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have hns' := mg_ns B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
    (mgLeft rl rr (kidsOf B rr.ws) sI sC)
  have hnmr : B.nm !! rr.nv.pgid' = some lr := by rw [hpgr]; exact hlr
  rcases h with ⟨y, ry, x, hy, hl, hx, hk, hbk, hv⟩ | ⟨c, q, pgq, j, hpos, ho, hpq, hlq, hj, hkq, hfq, hvq⟩
  · have hyp : y ≠ pl := by intro he; rw [he, hrp] at hy; cases hy; rw [hbr] at hl; cases hl
    by_cases hyl : y = ll
    · subst hyl; rw [hrl] at hy; cases hy
      exact Or.inl ⟨y, mgLeft rl rr (kidsOf B rr.ws) sI sC, x, by rw [hns', if_neg hyp, if_pos rfl], hl,
        List.mem_append.2 (Or.inl hx), hk, hbk, hv⟩
    by_cases hyr : y = lr
    · subst hyr; rw [hrr] at hy; cases hy
      exact Or.inl ⟨ll, mgLeft rl rr (kidsOf B rr.ws) sI sC, x, by rw [hns', if_neg hllp, if_pos rfl],
        by show rl.nv.isLeaf' = true; rw [hkind]; exact hl, List.mem_append.2 (Or.inr hx), hk, hbk, hv⟩
    by_cases hpr : ry.nv.parent' = lr
    · refine Or.inl ⟨y, { ry with nv := { ry.nv with parent' := ll } }, x,
        by rw [hns', if_neg hyp, if_neg hyl, if_neg hyr, hy]; simp only [Option.map_some, hpr, ↓reduceIte],
        hl, hx, hk, hbk, hv⟩
    · refine Or.inl ⟨y, ry, x,
        by rw [hns', if_neg hyp, if_neg hyl, if_neg hyr, hy]; simp only [Option.map_some, hpr, ↓reduceIte],
        hl, hx, hk, hbk, hv⟩
  · refine Or.inr ⟨c, q, pgq, j, ?_, ho, hpq, hlq, hj, hkq, hfq, hvq⟩
    unfold posRoot at hpos ⊢
    rcases hpos with h1 | ⟨y, j0, ⟨ry, x, hy, hyb, hx, hxc, hn⟩, hlt⟩
    · exact Or.inl h1
    right
    have hxn : x.pgid ≠ rr.nv.pgid' := by intro he; rw [hxc] at he; rw [he, hnmr] at hn; cases hn
    have hn' : (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)).nm !! W64 (c : Int) = none := by
      rw [mg_nm, if_neg (by rw [← hxc]; exact hxn)]; exact hn
    by_cases hyp : y = pl
    · subst y
      rw [hrp] at hy; cases hy
      have hji : j0 ≠ k + 1 := by intro he; subst he; rw [hwr] at hx; cases hx; exact hxn hpgr.symm
      refine ⟨pl, if j0 < k + 1 then j0 else j0 - 1, ⟨rmParent rp (k + 1) lr sI' sC', x,
        by rw [hns', if_pos rfl], hyb, ?_, hxc, hn'⟩, hlt⟩
      show (rp.ws.eraseIdx (k + 1))[if j0 < k + 1 then j0 else j0 - 1]? = some x
      rw [getElem?_eraseIdx']
      have : (if (if j0 < k + 1 then j0 else j0 - 1) < k + 1 then (if j0 < k + 1 then j0 else j0 - 1)
          else (if j0 < k + 1 then j0 else j0 - 1) + 1) = j0 := by
        by_cases h : j0 < k + 1
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg (by omega)]; omega
      rw [this]; exact hx
    by_cases hyl : y = ll
    · subst y; rw [hrl] at hy; cases hy
      refine ⟨ll, j0, ⟨mgLeft rl rr (kidsOf B rr.ws) sI sC, x, by rw [hns', if_neg hllp, if_pos rfl], hyb, ?_,
        hxc, hn'⟩, hlt⟩
      show (rl.ws ++ rr.ws)[j0]? = some x
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1]; exact hx
    by_cases hyr : y = lr
    · subst y; rw [hrr] at hy; cases hy
      refine ⟨ll, rl.ws.length + j0, ⟨mgLeft rl rr (kidsOf B rr.ws) sI sC, x,
        by rw [hns', if_neg hllp, if_pos rfl], by show rl.nv.isLeaf' = false; rw [hkind]; exact hyb, ?_,
        hxc, hn'⟩, hlt⟩
      show (rl.ws ++ rr.ws)[rl.ws.length + j0]? = some x
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hx
    by_cases hpr : ry.nv.parent' = lr
    · exact ⟨y, j0, ⟨{ ry with nv := { ry.nv with parent' := ll } }, x,
        by rw [hns', if_neg hyp, if_neg hyl, if_neg hyr, hy]; simp only [Option.map_some, hpr, ↓reduceIte],
        hyb, hx, hxc, hn'⟩, hlt⟩
    · exact ⟨y, j0, ⟨ry, x,
        by rw [hns', if_neg hyp, if_neg hyl, if_neg hyr, hy]; simp only [Option.map_some, hpr, ↓reduceIte],
        hyb, hx, hxc, hn'⟩, hlt⟩

end mg
end pure

section comb
variable [ext : FfiSyntax]

/-- Two siblings merged (`ll`, `lr`: the parent `pl`'s entries `k`, `k + 1`, one of them the
deficient node): the bucket in the invariant, the parent the deficient node. -/
theorem rbl_mg (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (pl : Loc) (rp : NRec) (k : Nat)
    (wl wr : WEntry) (ll lr : Loc) (rl rr : NRec) (nl : Loc) (sI sC sI' sC' : GoSlice)
    (HB : rblB W hwm bl B (some nl)) (hnl : nl = ll ∨ nl = lr) (hp0 : W.pages !! 0 = none)
    (hpn : pl ≠ null) (hrp : B.ns !! pl = some rp) (hbr : rp.nv.isLeaf' = false)
    (hwl : rp.ws[k]? = some wl) (hwr : rp.ws[k + 1]? = some wr)
    (hll : B.nm !! wl.pgid = some ll) (hlr : B.nm !! wr.pgid = some lr)
    (hrl : B.ns !! ll = some rl) (hrr : B.ns !! lr = some rr) (hne : 0 < (rl.ws ++ rr.ws).length) :
    rblB W hwm bl (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)) (some pl) ∧
      (∀ kk v, entryIn W B kk v → entryIn W (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)) kk v) ∧
      (∀ y ry', (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
          (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns !! y = some ry' → ry'.nv.unbalanced' = true →
        y = pl ∨ (y ≠ lr ∧ ∃ ry, B.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧ ry'.nv.pgid' = ry.nv.pgid')) ∧
      rl.nv.isLeaf' = rr.nv.isLeaf' := by
  obtain ⟨hc, ⟨bnd, hk⟩, ha, hht⟩ := HB
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, hpgl, hpgr, -⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  obtain ⟨-, -, kindp, pkd⟩ := (hk.2.2 pl rp hrp).2.2.1 hbr
  have hkind : rl.nv.isLeaf' = rr.nv.isLeaf' := by
    obtain ⟨r1, h1, k1⟩ := (pkd k wl hwl).1 ll hll
    obtain ⟨r2, h2, k2⟩ := (pkd (k + 1) wr hwr).1 lr hlr
    rw [hrl] at h1; cases h1; rw [hrr] at h2; cases h2; rw [k1, k2]
  have hroot0 : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc.2.2.2.2.2.2.1 h0 pl rp hrp; rw [hbr] at this; cases this
  have hleaf0 : rr.nv.isLeaf' = true → ∀ w ∈ rr.ws, B.nm !! w.pgid = none := by
    intro hl w hw
    have h0 := ((hk.2.2 lr rr hrr).2.2.2.2 hl w hw).1
    rw [h0]
    cases hn : B.nm !! W64 0 with
    | none => rfl
    | some l0 =>
      obtain ⟨-, r0, hr0, hpg0⟩ := hc.2.2.2.2.1 _ _ hn
      have hwf := (hc.2.2.2.2.2.2.2.1 l0 r0 hr0).2.2.2.2.2.2.2.2.1 hroot0
      rw [hpg0] at hwf
      cases hwf with
      | page _ pg _ hpg _ _ => rw [show uint.nat (W64 0) = 0 from rfl, hp0] at hpg; cases hpg
  have hroot : B.bv.rootNode' ≠ lr := by
    intro he; have := hk.2.1 rr (by rw [he]; exact hrr); rw [hp2] at this; exact hpn this
  have hdfc : some nl = some ll ∨ some nl = some lr := by rcases hnl with h | h <;> rw [h] <;> simp
  refine ⟨⟨mg_clean W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
      sI sC sI' sC' hkind (mg_lt W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr
        hrl hrr bnd _ hk) hleaf0 hroot,
    ⟨_, mg_keys W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
      sI sC sI' sC' hkind hleaf0 hroot hht bnd _ hk hdfc hne⟩,
    mg_acyc W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr sI sC sI' sC',
    mg_ht W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr sI sC sI' sC'
      hkind hht⟩,
    fun kk v h => mg_entryIn W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
      sI sC sI' sC' hkind kk v h,
    fun y ry' hy hu => mg_unbal W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl
      hrr sI sC sI' sC' y ry' hy hu, hkind⟩

end comb

section toks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

open Classical Iris.ProofMode in
/-- The tokens of two merged nodes: the merged one's, and the right one's page's. -/
theorem nodeToks_merge (γ : GName) (W : WView) (B B' : BRec) (rl rr rl' : NRec) (hbm : B'.bm = B.bm)
    (hp : rl'.nv.pgid' = rl.nv.pgid') (hws : rl'.ws = rl.ws ++ rr.ws) (hl : rl'.nv.isLeaf' = rl.nv.isLeaf')
    (hk : rr.nv.isLeaf' = rl.nv.isLeaf')
    (hnm : rl.nv.isLeaf' = false → ∀ x ∈ rl.ws ++ rr.ws, B'.nm !! x.pgid = B.nm !! x.pgid) :
    nodeToks (GF := GF) γ W B rl ∗ nodeToks γ W B rr ⊢ nodeToks γ W B' rl' ∗
      (if rr.nv.pgid' = W64 0 then emp else
        pgToks γ (GMap.filter (fun id _ => decide (id = uint.nat rr.nv.pgid')) W.pages)) := by
  unfold nodeToks
  rw [hp, hws, hl, opened_eq B B' hbm, hk]
  iintro ⟨⟨Ho, Hl⟩, ⟨Hor, Hr⟩⟩
  iframe Ho Hor
  iapply (BigSepL.bigSepL_append).2
  have hmono : ∀ (L : List WEntry), (∀ x ∈ L, rl.nv.isLeaf' = false → B'.nm !! x.pgid = B.nm !! x.pgid) →
      ∀ (s : Nat), ([∗list] k ↦ x ∈ L, (fun _ w => if rl.nv.isLeaf' = true then
        (if isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B w.key then
          pgToks (GF := GF) γ (treePages W.pages (inBucketRoot w.value)) else emp)
        else (if B.nm !! w.pgid = none then pgToks γ (xPages W.pages (opened B) (uint.nat w.pgid))
          else emp)) k x) ⊢
      [∗list] k ↦ x ∈ L, (fun _ w => if rl.nv.isLeaf' = true then
        (if isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B w.key then
          pgToks (GF := GF) γ (treePages W.pages (inBucketRoot w.value)) else emp)
        else (if B'.nm !! w.pgid = none then pgToks γ (xPages W.pages (opened B) (uint.nat w.pgid))
          else emp)) (k + s) x := by
    intro L hL s
    refine BigSepL.bigSepL_mono fun {j x} hx => ?_
    by_cases hlf : rl.nv.isLeaf' = true
    · simp only [hlf, ↓reduceIte]; exact .rfl
    · have hf : rl.nv.isLeaf' = false := by simpa using hlf
      simp only [hlf, Bool.false_eq_true, ↓reduceIte]
      rw [hL x (List.mem_of_getElem? hx) hf]
  isplitl [Hl]
  · iapply (hmono rl.ws (fun x hx hf => hnm hf x (List.mem_append.2 (Or.inl hx))) 0) $$ Hl
  · iapply (hmono rr.ws (fun x hx hf => hnm hf x (List.mem_append.2 (Or.inr hx))) rl.ws.length) $$ Hr

open Classical Iris.ProofMode in
/-- The tokens after the merge, and the right node's page's. -/
theorem mg_toks (γ : GName) (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (pl : Loc) (rp : NRec)
    (k : Nat) (wl wr : WEntry) (ll lr : Loc) (rl rr : NRec)
    (hc : bktClean W hwm bl B) (ha : rblAcyc B) (hpn : pl ≠ null) (hrp : B.ns !! pl = some rp)
    (hbr : rp.nv.isLeaf' = false)
    (hwl : rp.ws[k]? = some wl) (hwr : rp.ws[k + 1]? = some wr)
    (hll : B.nm !! wl.pgid = some ll) (hlr : B.nm !! wr.pgid = some lr)
    (hrl : B.ns !! ll = some rl) (hrr : B.ns !! lr = some rr) (sI sC sI' sC' : GoSlice)
    (hkind : rl.nv.isLeaf' = rr.nv.isLeaf') :
    bktToks (GF := GF) γ W B ⊢ bktToks γ W (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)) ∗
      (if rr.nv.pgid' = W64 0 then emp else
        pgToks γ (GMap.filter (fun id _ => decide (id = uint.nat rr.nv.pgid')) W.pages)) := by
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, hpgl, hpgr, -⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have honly := mg_only W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have hnm' := mg_nm B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
    (mgLeft rl rr (kidsOf B rr.ws) sI sC)
  have hrn : B.bv.rootNode' ≠ null := by
    intro h0; have := (hc.2.2.1 h0).1; rw [this] at hrp; cases hrp
  let f : NRec → NRec := fun x => if x.nv.parent' = lr then { x with nv := { x.nv with parent' := ll } } else x
  let D0 : GMap Loc NRec := GMap.delete pl (GMap.delete ll (GMap.delete lr B.ns))
  have hD0 : ∀ y, D0 !! y = if y = pl ∨ y = ll ∨ y = lr then none else B.ns !! y := by
    intro y
    show (GMap.delete pl (GMap.delete ll (GMap.delete lr B.ns))) !! y = _
    by_cases h1 : y = pl
    · subst h1; rw [GMap.lookup_delete, if_pos (Or.inl rfl)]
    rw [GMap.lookup_delete_ne _ (Ne.symm h1)]
    by_cases h2 : y = ll
    · subst h2; rw [GMap.lookup_delete, if_pos (Or.inr (Or.inl rfl))]
    rw [GMap.lookup_delete_ne _ (Ne.symm h2)]
    by_cases h3 : y = lr
    · subst h3; rw [GMap.lookup_delete, if_pos (Or.inr (Or.inr rfl))]
    rw [GMap.lookup_delete_ne _ (Ne.symm h3), if_neg (by rintro (h | h | h) <;> contradiction)]
  have he : (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns =
      <[pl := rmParent rp (k + 1) lr sI' sC']> (<[ll := mgLeft rl rr (kidsOf B rr.ws) sI sC]>
        (GMap.fmap f D0)) := by
    apply GMap.ext; intro y
    rw [mg_ns]
    rw [rf_lookup, rf_lookup, GMap.lookup_fmap, hD0]
    by_cases h1 : y = pl
    · rw [if_pos h1, if_pos h1]
    rw [if_neg h1, if_neg h1]
    by_cases h2 : y = ll
    · rw [if_pos h2, if_pos h2]
    rw [if_neg h2, if_neg h2]
    by_cases h3 : y = lr
    · rw [if_pos h3, if_pos (Or.inr (Or.inr h3))]; rfl
    rw [if_neg h3, if_neg (by rintro (h | h | h) <;> contradiction)]
  have hlook : ∀ y, y = pl ∨ y = ll ∨ y = lr → D0 !! y = none := fun y h => by rw [hD0, if_pos h]
  unfold bktToks
  rw [if_neg hrn]
  show _ ⊢ (if B.bv.rootNode' = null then _ else _) ∗ _
  rw [if_neg hrn, he]
  have g1 : Std.get? B.ns lr = some rr := hrr
  have g2 : Std.get? (Std.delete B.ns lr) ll = some rl := by
    show (GMap.delete lr B.ns) !! ll = _; rw [GMap.lookup_delete_ne _ (Ne.symm hllr)]; exact hrl
  have g3 : Std.get? (Std.delete (Std.delete B.ns lr) ll) pl = some rp := by
    show (GMap.delete ll (GMap.delete lr B.ns)) !! pl = _
    rw [GMap.lookup_delete_ne _ hllp, GMap.lookup_delete_ne _ hlrp]; exact hrp
  have hnmLR : rl.nv.isLeaf' = false → ∀ x ∈ rl.ws ++ rr.ws,
      (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)).nm !! x.pgid = B.nm !! x.pgid := by
    intro hb' x hx
    have hbr2 : rr.nv.isLeaf' = false := by rw [← hkind]; exact hb'
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
      have hxn : x.pgid ≠ rr.nv.pgid' := fun he => hllp (honly ll rl j x hrl hb' hj (by rw [he, hpgr])).1
      rw [hnm', if_neg hxn]
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
      have hxn : x.pgid ≠ rr.nv.pgid' := fun he => hlrp (honly lr rr j x hrr hbr2 hj (by rw [he, hpgr])).1
      rw [hnm', if_neg hxn]
  have hfm : (GMap.fmap f D0 : GMap Loc NRec) = Iris.Std.PartialMap.map f D0 := by
    apply GMap.ext; intro y
    show (GMap.fmap f D0) !! y = Std.get? (Iris.Std.PartialMap.map f D0) y
    rw [GMap.lookup_fmap, Iris.Std.LawfulPartialMap.get?_map]; rfl
  iintro H
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r) g1).1 $$ H
    with ⟨Hr, H⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r) g2).1 $$ H
    with ⟨Hl, H⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r) g3).1 $$ H
    with ⟨Hp, H⟩
  icases nodeToks_merge γ W B (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)) rl rr (mgLeft rl rr (kidsOf B rr.ws) sI sC) rfl rfl rfl rfl
      hkind.symm hnmLR $$ [Hl Hr] with ⟨Hl, Hown⟩
  · iframe
  · iframe Hown
    iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun _ x => nodeToks (GF := GF) γ W
      (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC') (mgLeft rl rr (kidsOf B rr.ws) sI sC)) x)
      (show Std.get? (<[ll := mgLeft rl rr (kidsOf B rr.ws) sI sC]> (GMap.fmap f D0)) pl = none by
        show (<[ll := mgLeft rl rr (kidsOf B rr.ws) sI sC]> (GMap.fmap f D0)) !! pl = none
        rw [rf_lookup, if_neg (Ne.symm hllp), GMap.lookup_fmap, hlook pl (Or.inl rfl)]; rfl)).2
    isplitl [Hp]
    · iapply nodeToks_erase γ W B (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)) rp (rmParent rp (k + 1) lr sI' sC') (k + 1) rfl rfl rfl rfl ?_ $$ Hp
      intro _ x hx
      obtain ⟨j, hji, hj⟩ := List.mem_eraseIdx_iff_getElem?.1 hx
      have hxn : x.pgid ≠ rr.nv.pgid' := fun he => hji (honly pl rp j x hrp hbr hj (by rw [he, hpgr])).2
      rw [hnm', if_neg hxn]
    iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun _ x => nodeToks (GF := GF) γ W
      (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC') (mgLeft rl rr (kidsOf B rr.ws) sI sC)) x)
      (show Std.get? (GMap.fmap f D0) ll = none by
        show (GMap.fmap f D0) !! ll = none
        rw [GMap.lookup_fmap, hlook ll (Or.inr (Or.inl rfl))]; rfl)).2
    iframe Hl
    rw [hfm, BigSepM.bigSepM_map]
    have hD0' : (Std.delete (Std.delete (Std.delete B.ns lr) ll) pl : GMap Loc NRec) = D0 := rfl
    rw [hD0']
    iapply (BigSepM.bigSepM_mono (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r)
      (Ψ := fun _ x => nodeToks (GF := GF) γ W (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)) (f x)) ?_) $$ H
    intro y ry hy
    change D0 !! y = some ry at hy
    rw [hD0] at hy
    split at hy
    · cases hy
    rename_i hyn
    have hyp : y ≠ pl := fun h => hyn (Or.inl h)
    refine BIBase.Entails.trans (nodeToks_congr γ W B (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC') (mgLeft rl rr (kidsOf B rr.ws) sI sC)) ry ry rfl rfl rfl rfl ?_) ?_
    · intro hlf x hx
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
      have hxn : x.pgid ≠ rr.nv.pgid' := fun he => hyp (honly y ry j x hy hlf hj (by rw [he, hpgr])).1
      rw [hnm', if_neg hxn]
    · show nodeToks γ W _ ry ⊢ nodeToks γ W _ (if ry.nv.parent' = lr then _ else ry)
      split
      · exact (BiEntails.of_eq (nodeToks_eq γ W (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC') (mgLeft rl rr (kidsOf B rr.ws) sI sC)) (mgBkt B pl ll lr rr.nv.pgid' (rmParent rp (k + 1) lr sI' sC') (mgLeft rl rr (kidsOf B rr.ws) sI sC)) ry _ rfl rfl rfl rfl rfl)).2
      · exact .rfl

end toks

end bbolt
end EtcdGrove
end Perennial
