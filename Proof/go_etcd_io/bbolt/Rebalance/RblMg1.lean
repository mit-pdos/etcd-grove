/-
Two siblings merged by `node.rebalance` (`ll`, `lr`: the children of the parent `pl` at its
entries `k`, `k + 1`): the definitions (`reparent`, `kidsOf`, `mgLeft`, `mgParent`, `mgBkt`) and
the pure lemmas on lists and bounds the merge's proofs use. Ported from
`old/bbolt/.../RebalanceMg.lean` (with the few helpers of `RebalanceRm`, `ShapeMat`, `WriteLeaf`
it uses, under names of their own: `RblRm.lean` ports those separately).

`mgParent` is the old `RebalanceRm.rmParent` (the parent after `del` of its entry `i` and
`removeChild` of `c`), as a record update (the parent keeps its `capOwn`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblStart
public import Proof.go_etcd_io.bbolt.Read.TreeFacts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rbl
variable [GooseExts]

/-! ### The merge -/

/-- The nodes `ns` with the children of `a` reparented to `b`. -/
def reparent (ns : GMap Loc NRec) (a b : Loc) : GMap Loc NRec :=
  GMap.fmap (fun x => if x.nv.parent' = a then { x with nv := { x.nv with parent' := b } } else x) ns

/-- The materialized children of the entries `ws`, in order. -/
def kidsOf (B : BRec) (ws : List WEntry) : List Loc := ws.filterMap fun w => B.nm !! w.pgid

/-- The left node after the merge (its slices `sI`, `sC`). -/
def mgLeft (rl rr : NRec) (moved : List Loc) (sI sC : GoSlice) : NRec :=
  { rl with
    nv := { rl.nv with inodes' := sI, children' := sC }, ins := rl.ins ++ rr.ins,
    ws := rl.ws ++ rr.ws, cs := rl.cs ++ moved }

/-- The parent `rp` after `del` of its entry `i` and `removeChild` of `c` (its slices `sI`,
`sC`): the old `rmParent`. -/
def mgParent (rp : NRec) (i : Nat) (c : Loc) (sI sC : GoSlice) : NRec :=
  { rp with
    nv := { rp.nv with inodes' := sI, unbalanced' := true, children' := sC },
    ins := rp.ins.eraseIdx i, ws := rp.ws.eraseIdx i, cs := rp.cs.eraseIdx (rp.cs.idxOf c) }

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

/-! ### Helpers (lists, entries, bounds) -/

theorem wKey_get_mg (ws : List WEntry) (i : Nat) (h : i < ws.length) : wKey ws i = ws[i].key := by
  unfold wKey; rw [List.getElem?_eq_getElem h]; rfl

/-- `wEntryBnd` in terms of `wKey` (the old `entryBnd` on entries). -/
theorem wEntryBnd_mg (b : Option (List w8) × Option (List w8)) (ws : List WEntry) (i : Nat) :
    wEntryBnd b ws i = (childLo b.1 (wKey ws) i, childHi b.2 (wKey ws) ws.length i) := by
  have hk : (fun j => (ws.map WEntry.key).getD j []) = wKey ws := by
    funext j; unfold wKey; rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  unfold wEntryBnd entryBnd; rw [hk, List.length_map]

theorem nodup_pgid_ne_mg (ws : List WEntry) (h : (ws.map WEntry.pgid).Nodup) (i k : Nat)
    (w x : WEntry) (hi : ws[i]? = some w) (hk : ws[k]? = some x) (hne : k ≠ i) :
    x.pgid ≠ w.pgid := by
  intro he
  have hkl := (List.getElem?_eq_some_iff.1 hk).1
  have h1 : (ws.map WEntry.pgid)[k]? = some x.pgid := by rw [List.getElem?_map, hk]; rfl
  have h2 : (ws.map WEntry.pgid)[i]? = some w.pgid := by rw [List.getElem?_map, hi]; rfl
  rw [he] at h1
  exact hne ((List.Nodup.getElem?_inj (by simpa using hkl) h).1 (h1.trans h2.symm))

theorem branch_ne_leaf_mg : branchPageFlag ≠ leafPageFlag := by
  unfold branchPageFlag leafPageFlag; decide

theorem cs_erase_mg (cs : List Loc) (c : Loc) : cs.eraseIdx (cs.idxOf c) = cs.erase c :=
  (List.erase_eq_eraseIdx_of_idxOf rfl).symm

theorem nm_inj_mg (v : View) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean v hwm bl B)
    (a b : w64) (x : Loc) (ha : B.nm !! a = some x) (hb : B.nm !! b = some x) : a = b := by
  obtain ⟨-, r1, h1, p1⟩ := hc.2.2.2.2.1 a x ha
  obtain ⟨-, r2, h2, p2⟩ := hc.2.2.2.2.1 b x hb
  rw [h1] at h2; cases h2; rw [← p1, p2]

theorem mem_eraseIdx_of_ne_mg {α : Type} (l : List α) (i : Nat) (x : α) (hx : x ∈ l)
    (hne : l[i]? ≠ some x) : x ∈ l.eraseIdx i := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
  rw [List.mem_eraseIdx_iff_getElem?]
  exact ⟨j, by rintro rfl; exact hne hj, hj⟩

theorem getElem?_eraseIdx_mg {α : Type} (l : List α) (i j : Nat) :
    (l.eraseIdx i)[j]? = l[if j < i then j else j + 1]? := by
  rw [List.getElem?_eraseIdx]; split <;> rfl

theorem wsSorted_iff_mg (ws : List WEntry) :
    wsSorted ws ↔ ws.Pairwise (fun a b => go.GoStringLt a.key b.key) := by
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij
    have := h i j hij hj
    rwa [wKey_get_mg ws i hi, wKey_get_mg ws j hj] at this
  · intro h i j hij hj
    rw [wKey_get_mg ws i (by omega), wKey_get_mg ws j hj]
    exact h i j (by omega) hj hij

theorem wsSorted_eraseIdx_mg (ws : List WEntry) (i : Nat) (h : wsSorted ws) :
    wsSorted (ws.eraseIdx i) := by
  rw [wsSorted_iff_mg] at h ⊢
  exact h.sublist (List.eraseIdx_sublist ws i)

/-- The bounds of a branch's entries after one is removed (the bounds of the branch tightened
to its new first key when it was the first) are looser (the old `entryBnd_erase`). -/
theorem wEntryBnd_erase_mg (ws : List WEntry) (i : Nat) (b : Option (List w8) × Option (List w8))
    (hs : wsSorted ws) (hk : ∀ w ∈ ws, keyIn b.1 b.2 w.key) (h2 : 2 ≤ ws.length) (hi : i < ws.length)
    (j' : Nat) (hj' : j' < ws.length) (hne : j' ≠ i) :
    bndIn (wEntryBnd b ws j')
      (wEntryBnd (if i = 0 then (some (wKey ws 1), b.2) else b) (ws.eraseIdx i)
        (if j' < i then j' else j' - 1)) := by
  obtain ⟨k, hkdef, hkc⟩ : ∃ k, (if j' < i then j' else j' - 1) = k ∧
      ((j' < i ∧ k = j') ∨ (i < j' ∧ k = j' - 1)) := by
    by_cases h : j' < i
    · exact ⟨j', if_pos h, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨j' - 1, if_neg h, Or.inr ⟨by omega, rfl⟩⟩
  rw [hkdef]
  have hlen : (ws.eraseIdx i).length = ws.length - 1 := List.length_eraseIdx_of_lt hi
  have hwk : ∀ j, wKey (ws.eraseIdx i) j = wKey ws (if j < i then j else j + 1) := by
    intro j; unfold wKey; rw [getElem?_eraseIdx_mg]
  have hkin : ∀ j, j < ws.length → keyIn b.1 b.2 (wKey ws j) := by
    intro j hj; rw [wKey_get_mg ws j hj]; exact hk _ (List.getElem_mem hj)
  have hsrt : ∀ a c, a < c → c < ws.length → go.GoStringLt (wKey ws a) (wKey ws c) := hs
  have hk0 : (if k < i then k else k + 1) = j' := by
    rcases hkc with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · rw [if_pos h1]
    · rw [if_neg (by omega)]; omega
  have hk1 : k + 1 < ws.length - 1 → (if k + 1 < i then k + 1 else k + 1 + 1) =
      (if j' + 1 = i then j' + 2 else j' + 1) := by
    intro _
    rcases hkc with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · by_cases hc : k + 1 = i
      · rw [if_neg (by omega), if_pos hc]
      · rw [if_pos (by omega), if_neg hc]
    · rw [if_neg (by omega), if_neg (by omega)]; omega
  rw [wEntryBnd_mg, wEntryBnd_mg]
  unfold childLo childHi
  rw [hlen]
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · -- the lower bound: the same
    simp only at hy ⊢
    by_cases hj0 : k = 0
    · rw [if_pos hj0] at hy
      by_cases hi0 : i = 0
      · rw [if_pos hi0] at hy; simp only at hy; cases hy
        have hj1 : j' = 1 := by rcases hkc with ⟨h1, -⟩ | ⟨-, h1⟩ <;> omega
        rw [if_neg (by omega), hj1]; exact ⟨_, rfl, rk_le_refl _⟩
      · rw [if_neg hi0] at hy
        have hj1 : j' = 0 := by rcases hkc with ⟨-, h1⟩ | ⟨h1, h1'⟩ <;> omega
        rw [if_pos hj1]; exact ⟨y, hy, rk_le_refl y⟩
    · rw [if_neg hj0] at hy; cases hy
      have hjp : j' ≠ 0 := by rcases hkc with ⟨-, h1⟩ | ⟨h1, h1'⟩ <;> omega
      rw [if_neg hjp, hwk, hk0]
      exact ⟨_, rfl, rk_le_refl _⟩
  · -- the upper bound: looser
    simp only at hy ⊢
    by_cases hlt : k + 1 < ws.length - 1
    · rw [if_pos hlt] at hy; cases hy
      rw [hwk, hk1 hlt]
      rw [if_pos (show j' + 1 < ws.length by rcases hkc with ⟨-, h1⟩ | ⟨h1, h1'⟩ <;> omega)]
      by_cases hc : j' + 1 = i
      · rw [if_pos hc]
        exact ⟨_, rfl, rk_le_of_lt (hsrt _ _ (by omega)
          (by rcases hkc with ⟨-, h1⟩ | ⟨h1, h1'⟩ <;> omega))⟩
      · rw [if_neg hc]; exact ⟨_, rfl, rk_le_refl _⟩
    · rw [if_neg hlt] at hy
      have hyb : b.2 = some y := by split at hy <;> exact hy
      by_cases hc : j' + 1 < ws.length
      · rw [if_pos hc]
        exact ⟨_, rfl, rk_le_of_lt ((hkin _ hc).2 y hyb)⟩
      · rw [if_neg hc]; exact ⟨y, hyb, rk_le_refl y⟩

/-! ### Keys and bounds of the merged node -/

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
    bndIn (wEntryBnd bl L j) (wEntryBnd b' (L ++ R) j) := by
  rw [wEntryBnd_mg, wEntryBnd_mg]
  unfold childLo childHi
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
    bndIn (wEntryBnd br R j) (wEntryBnd b' (L ++ R) (L.length + j)) := by
  rw [wEntryBnd_mg, wEntryBnd_mg]
  unfold childLo childHi
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
theorem kidLeaf (v : View) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean v hwm bl B)
    (ht : Loc → Nat) (pht : Nat → Nat) (hp : pageHts v.pages pht)
    (hh : ∀ l r, B.ns !! l = some r → (r.nv.isLeaf' = true → ht l = 0) ∧
      (r.nv.isLeaf' = false → ∀ w ∈ r.ws, (∀ l', B.nm !! w.pgid = some l' → ht l' + 1 = ht l) ∧
        (B.nm !! w.pgid = none → pht w.pgid.toNat + 1 = ht l)))
    (y : Loc) (ry : NRec) (hy : B.ns !! y = some ry) (hb : ry.nv.isLeaf' = false) (x : WEntry)
    (hx : x ∈ ry.ws) :
    (∀ l' r', B.nm !! x.pgid = some l' → B.ns !! l' = some r' → r'.nv.isLeaf' = decide (ht y = 1)) ∧
    (B.nm !! x.pgid = none → ∀ pg, v.pages !! x.pgid.toNat = some pg → 0 < pageCount pg →
      decide (pageFlags pg = leafPageFlag) = decide (ht y = 1)) := by
  obtain ⟨a1, a2⟩ := (hh y ry hy).2 hb x hx
  refine ⟨fun l' r' hl' hr' => ?_, fun hn pg hpg hcnt => ?_⟩
  · have e := a1 l' hl'
    rcases (Bool.eq_false_or_eq_true r'.nv.isLeaf').symm with h | h
    · -- a branch child: it has a child, so its height is positive
      have hcl := (hc.2.2.2.2.2.2.2.1 l' r' hr').2.2.2.2.2.2.2.2.2.2.2.2.1 h
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
    have hwf := (((hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.2.1 hb).2.2 x hx).2.2 hn
    obtain ⟨-, -, -, -, hk⟩ := Read.treeWF_page _ _ _ hwf pg hpg
    obtain ⟨p1, p2⟩ := hp _ pg hpg
    rcases hk with hbp | hl
    · have hnl : pageFlags pg ≠ leafPageFlag := by rw [hbp]; exact branch_ne_leaf_mg
      rw [decide_eq_false hnl]; symm; simp only [decide_eq_false_iff_not]
      have := p2 hbp 0 hcnt; omega
    · rw [decide_eq_true hl]; symm; simp only [decide_eq_true_eq]; have := p1 hl; omega

theorem entryBnd_mid (b : Option (List w8) × Option (List w8)) (ws : List WEntry) (k : Nat)
    (w : WEntry) (h : ws[k + 1]? = some w) :
    (wEntryBnd b ws k).2 = some w.key ∧ (wEntryBnd b ws (k + 1)).1 = some w.key := by
  have hl := (List.getElem?_eq_some_iff.1 h).1
  have hk : wKey ws (k + 1) = w.key := by unfold wKey; rw [h]; rfl
  rw [wEntryBnd_mg, wEntryBnd_mg]
  unfold childLo childHi
  simp only
  rw [if_pos hl, if_neg (by omega), hk]; exact ⟨rfl, rfl⟩

/-- The merged node's bounds: the left one's low (its entry's, a leaf), the right one's entry's
high. -/
def mgBnd (bnd : Loc → Option (List w8) × Option (List w8)) (pl ll : Loc) (rp rl : NRec) (k : Nat) :
    Loc → Option (List w8) × Option (List w8) :=
  fun x => if x = ll then ((if rl.nv.isLeaf' then (wEntryBnd (bnd pl) rp.ws k).1 else (bnd ll).1),
    (wEntryBnd (bnd pl) rp.ws (k + 1)).2) else bnd x

end rbl

end bbolt
end EtcdGrove
end Perennial
