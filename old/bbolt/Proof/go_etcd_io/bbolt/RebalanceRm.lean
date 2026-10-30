/-
An empty leaf removed by `node.rebalance` (`n.parent.del(n.key)`, `n.parent.removeChild(n)`,
`delete(b.nodes, n.pgid)`, `n.free()`): the bucket `rmBkt` stays clean, its keys stay with the
parent the deficient node (its bounds tightened to its new first key if it lost its first entry),
the nested buckets' entries stay (the leaf had none), and the leaf's page token is given up.
-/
module

public import Proof.go_etcd_io.bbolt.RebalanceMat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The parent `rp` after `del` of its entry `i` and `removeChild` of `c` (its slices `sI`,
`sC`). -/
def rmParent (rp : NRec) (i : Nat) (c : Loc) (sI sC : GoSlice) : NRec :=
  ⟨{ rp.nv with inodes' := sI, unbalanced' := true, children' := sC }, rp.ins.eraseIdx i,
    rp.ws.eraseIdx i, rp.cs.eraseIdx (rp.cs.idxOf c), rp.key, rp.ksrc⟩

/-- The bucket with the node `nl` (page `pgid`) removed and its parent `pl` now `rp'`. -/
def rmBkt (B : BRec) (nl pl : Loc) (pgid : w64) (rp' : NRec) : BRec :=
  { B with nm := GMap.delete pgid B.nm, ns := <[pl := rp']> (GMap.delete nl B.ns) }

theorem rm_ns (B : BRec) (nl pl : Loc) (pgid : w64) (rp' : NRec) (y : Loc) :
    (rmBkt B nl pl pgid rp').ns !! y = if y = pl then some rp' else if y = nl then none else B.ns !! y := by
  show (<[pl := rp']> (GMap.delete nl B.ns)) !! y = _
  rw [rf_lookup]
  split
  · rfl
  · by_cases h : y = nl
    · subst h; rw [if_pos rfl, GMap.lookup_delete]
    · rw [if_neg h, GMap.lookup_delete_ne _ (Ne.symm h)]

theorem rm_nm (B : BRec) (nl pl : Loc) (pgid : w64) (rp' : NRec) (k : w64) :
    (rmBkt B nl pl pgid rp').nm !! k = if k = pgid then none else B.nm !! k := by
  show (GMap.delete pgid B.nm) !! k = _
  split
  · rename_i h; subst h; rw [GMap.lookup_delete]
  · rw [GMap.lookup_delete_ne _ (Ne.symm ‹_›)]

theorem cs_erase (cs : List Loc) (c : Loc) : cs.eraseIdx (cs.idxOf c) = cs.erase c :=
  (List.erase_eq_eraseIdx_of_idxOf rfl).symm

theorem nm_inj (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (a b : w64) (x : Loc) (ha : B.nm !! a = some x) (hb : B.nm !! b = some x) : a = b := by
  obtain ⟨-, r1, h1, p1⟩ := hc.2.2.2.2.1 a x ha
  obtain ⟨-, r2, h2, p2⟩ := hc.2.2.2.2.1 b x hb
  rw [h1] at h2; cases h2; rw [← p1, p2]

theorem mem_eraseIdx_of_ne {α : Type} (l : List α) (i : Nat) (x : α) (hx : x ∈ l)
    (hne : l[i]? ≠ some x) : x ∈ l.eraseIdx i := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
  rw [List.mem_eraseIdx_iff_getElem?]
  exact ⟨j, by rintro rfl; exact hne hj, hj⟩

theorem getElem?_eraseIdx' {α : Type} (l : List α) (i j : Nat) :
    (l.eraseIdx i)[j]? = l[if j < i then j else j + 1]? := by
  rw [List.getElem?_eraseIdx]; split <;> rfl

/-- The bounds of a branch's entries after one is removed (the bounds of the branch tightened
to its new first key when it was the first) are looser. -/
theorem entryBnd_erase (ws : List WEntry) (i : Nat) (b : Option (List w8) × Option (List w8))
    (hs : wsSorted ws) (hk : ∀ w ∈ ws, keyIn b.1 b.2 w.key) (h2 : 2 ≤ ws.length) (hi : i < ws.length)
    (j' : Nat) (hj' : j' < ws.length) (hne : j' ≠ i) :
    bndIn (entryBnd b ws j')
      (entryBnd (if i = 0 then (some (wKey ws 1), b.2) else b) (ws.eraseIdx i)
        (if j' < i then j' else j' - 1)) := by
  obtain ⟨k, hkdef, hkc⟩ : ∃ k, (if j' < i then j' else j' - 1) = k ∧
      ((j' < i ∧ k = j') ∨ (i < j' ∧ k = j' - 1)) := by
    by_cases h : j' < i
    · exact ⟨j', if_pos h, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨j' - 1, if_neg h, Or.inr ⟨by omega, rfl⟩⟩
  rw [hkdef]
  have hlen : (ws.eraseIdx i).length = ws.length - 1 := List.length_eraseIdx_of_lt hi
  have hwk : ∀ j, wKey (ws.eraseIdx i) j = wKey ws (if j < i then j else j + 1) := by
    intro j; unfold wKey; rw [getElem?_eraseIdx']
  have hkin : ∀ j, j < ws.length → keyIn b.1 b.2 (wKey ws j) := by
    intro j hj; rw [wKey_get ws j hj]; exact hk _ (List.getElem_mem hj)
  have hsrt : ∀ a c, a < c → c < ws.length → go.GoStringLt (wKey ws a) (wKey ws c) := hs
  have hidx : ∀ m, (if m < i then m else m + 1) = (if m < i then m else m + 1) := fun _ => rfl
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
  clear hidx
  unfold entryBnd childLo childHi
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

section rm
variable (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (nl : Loc) (r : NRec) (pl : Loc) (rp : NRec)
  (i : Nat) (w : WEntry) (sI sC : GoSlice)
  (hc : bktClean W hwm bl B) (hr : B.ns !! nl = some r) (hleaf : r.nv.isLeaf' = true)
  (hemp : r.ws = []) (hpl : r.nv.parent' = pl) (hpn : pl ≠ null) (hrp : B.ns !! pl = some rp)
  (hw : rp.ws[i]? = some w) (hwp : w.pgid = r.nv.pgid') (hroot : B.bv.rootNode' ≠ nl)
  (hnself : rp.nv.parent' ≠ pl)
include hc hr hleaf hpl hpn hrp hw hwp

theorem rm_basic :
    rp.nv.isLeaf' = false ∧ nl ∈ rp.cs ∧ nl ≠ pl ∧ B.nm !! r.nv.pgid' = some nl ∧
      B.nm !! rp.nv.pgid' = some pl ∧ rp.nv.pgid' ≠ r.nv.pgid' ∧
      (∀ y ry, B.ns !! y = some ry → ry.nv.parent' ≠ nl) ∧
      (∀ y ry j w', B.ns !! y = some ry → ry.nv.isLeaf' = false → ry.ws[j]? = some w' →
        w'.pgid = r.nv.pgid' → y = pl ∧ j = i) ∧
      (rp.ws.map WEntry.pgid).Nodup ∧ B.ib.root' ≠ W64 0 := by
  have hn := hc.2.2.2.2.2.2.2.1 nl r hr
  obtain ⟨rp0, hrp0, hbr, hin, -⟩ := hn.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by rw [hpl]; exact hpn)
  rw [hpl, hrp] at hrp0; cases hrp0
  have hnlpl : nl ≠ pl := by intro h; rw [h, hrp] at hr; cases hr; rw [hleaf] at hbr; cases hbr
  have hnm1 := hn.2.2.2.2.2.2.1
  have hnp := hc.2.2.2.2.2.2.2.1 pl rp hrp
  have hnm2 := hnp.2.2.2.2.2.2.1
  have hpg : rp.nv.pgid' ≠ r.nv.pgid' := by
    intro he; rw [he, hnm1] at hnm2; cases hnm2; exact hnlpl rfl
  have hnotp : ∀ y ry, B.ns !! y = some ry → ry.nv.parent' ≠ nl := by
    intro y ry hy he
    obtain ⟨rq, hrq, hbq, -⟩ := (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [he]; intro h0; rw [h0] at hr
          obtain ⟨-, -, -, -, -, -, h7, -⟩ := hn
          exact (hc.2.2.2.2.1 _ _ h7).1 h0)
    rw [he, hr] at hrq; cases hrq; rw [hleaf] at hbq; cases hbq
  obtain ⟨-, hnd, hkids⟩ := hnp.2.2.2.2.2.2.2.2.2.2.2.1 hbr
  have hroot0 : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc.2.2.2.2.2.2.1 h0 pl rp hrp; rw [hbr] at this; cases this
  refine ⟨hbr, hin, hnlpl, hnm1, hnm2, hpg, hnotp, ?_, hnd, hroot0⟩
  intro y ry j w' hy hyb hj hwj
  obtain ⟨-, -, hk⟩ := (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.1 hyb
  obtain ⟨-, hs, -⟩ := hk w' (List.mem_of_getElem? hj)
  rw [hwj] at hs
  obtain ⟨r1, hr1, hp1⟩ := hs nl hnm1
  rw [hr] at hr1; cases hr1
  rw [hpl] at hp1
  subst hp1
  rw [hrp] at hy; cases hy
  refine ⟨rfl, ?_⟩
  have := nodup_pgid_ne rp.ws hnd i j w w' hw hj
  by_cases hji : j = i
  · exact hji
  · exact absurd (by rw [hwj, hwp]) (this hji)

/-- A page position after the removal was one before (the parent's entries shifted). -/
theorem rm_pos (h2 : 2 ≤ rp.ws.length) (y : Loc) (j : Nat) (c : w64)
    (hp : pagePosAt (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)) y j c) :
    pagePosAt B y (if y = pl then (if j < i then j else j + 1) else j) c := by
  obtain ⟨hbr, hin, hnlpl, hnm1, hnm2, hpg, hnotp, honly, hnd, hroot0⟩ :=
    rm_basic W hwm bl B nl r pl rp i w hc hr hleaf hpl hpn hrp hw hwp
  obtain ⟨ry', w', hy, hb, hw', hc', hn⟩ := hp
  rw [rm_nm] at hn
  have hcn : c ≠ r.nv.pgid' := by
    intro he
    rw [rm_ns] at hy
    split at hy
    · rename_i hyp
      cases hy
      obtain ⟨j', hj'i, hj'⟩ : ∃ j', j' ≠ i ∧ rp.ws[j']? = some w' := by
        rw [← List.mem_eraseIdx_iff_getElem?]; exact List.mem_of_getElem? hw'
      exact hj'i (honly pl rp j' w' hrp hbr hj' (by rw [hc', he])).2
    · split at hy
      · cases hy
      · rename_i hyp _
        exact hyp (honly y ry' j w' hy hb hw' (by rw [hc', he])).1
  rw [if_neg hcn] at hn
  rw [rm_ns] at hy
  split at hy
  · rename_i hyp
    cases hy; subst y
    rw [if_pos rfl]
    refine ⟨rp, w', hrp, hb, ?_, hc', hn⟩
    rw [← getElem?_eraseIdx']; exact hw'
  · rename_i hyp
    split at hy
    · cases hy
    rw [if_neg hyp]
    exact ⟨ry', w', hy, hb, hw', hc', hn⟩

/-- The removed bucket's old nodes (but the leaf) and their new records. -/
theorem rm_old (h2 : 2 ≤ rp.ws.length) (y : Loc) (ry : NRec) (hy : B.ns !! y = some ry) (hyn : y ≠ nl) :
    ∃ ry', (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)).ns !! y = some ry' ∧
      ry'.nv.parent' = ry.nv.parent' ∧ ry'.nv.isLeaf' = ry.nv.isLeaf' ∧ ry'.nv.pgid' = ry.nv.pgid' ∧
      (y ≠ pl → ry' = ry) := by
  rw [rm_ns]
  by_cases hyp : y = pl
  · subst hyp; rw [hrp] at hy; cases hy
    exact ⟨rmParent rp i nl sI sC, by rw [if_pos rfl], rfl, rfl, rfl, fun h => absurd rfl h⟩
  · rw [if_neg hyp, if_neg hyn]; exact ⟨ry, hy, rfl, rfl, rfl, fun _ => rfl⟩

include hroot hnself in
theorem rm_clean (h2 : 2 ≤ rp.ws.length) :
    bktClean W hwm bl (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)) := by
  obtain ⟨hbr, hin, hnlpl, hnm1, hnm2, hpg, hnotp, honly, hnd, hroot0⟩ :=
    rm_basic W hwm bl B nl r pl rp i w hc hr hleaf hpl hpn hrp hw hwp
  have hold := rm_old W hwm bl B nl r pl rp i w sI sC hc hr hleaf hpl hpn hrp hw hwp h2
  have hpos := rm_pos W hwm bl B nl r pl rp i w sI sC hc hr hleaf hpl hpn hrp hw hwp h2
  have hnm' := rm_nm B nl pl r.nv.pgid' (rmParent rp i nl sI sC)
  have hns' := rm_ns B nl pl r.nv.pgid' (rmParent rp i nl sI sC)
  have hinj := nm_inj W hwm bl B hc
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc
  have hrn : B.bv.rootNode' ≠ null := by
    intro h0; have := (c3 h0).1; rw [this] at hr; cases hr
  have hil : i < rp.ws.length := (List.getElem?_eq_some_iff.1 hw).1
  have hnp := c8 pl rp hrp
  have hilen : rp.ins.length = rp.ws.length := hnp.2.1
  -- the entries of the parent after the removal are its others
  have hmem' : ∀ x, x ∈ rp.ws.eraseIdx i → x ∈ rp.ws ∧ x.pgid ≠ r.nv.pgid' := by
    intro x hx
    obtain ⟨j, hji, hj⟩ := List.mem_eraseIdx_iff_getElem?.1 hx
    refine ⟨List.mem_of_getElem? hj, fun he => hji ?_⟩
    exact (honly pl rp j x hrp hbr hj he).2
  have hmemw : ∀ x, x ∈ rp.ws → x.pgid ≠ r.nv.pgid' → x ∈ rp.ws.eraseIdx i := by
    intro x hx hne
    exact mem_eraseIdx_of_ne rp.ws i x hx (by rw [hw]; intro h; cases h; exact hne hwp)
  have hcs' : ∀ c, c ∈ rp.cs.eraseIdx (rp.cs.idxOf nl) ↔ c ≠ nl ∧ c ∈ rp.cs := by
    intro c; rw [cs_erase]; exact List.Nodup.mem_erase_iff hnp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- a child's node, after the removal
  have hchild : ∀ (q : Loc) (l' : Loc) (k : w64), B.nm !! k = some l' → k ≠ r.nv.pgid' →
      (∀ r', B.ns !! l' = some r' → r'.nv.parent' = q) →
      ∃ r', (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)).ns !! l' = some r' ∧ r'.nv.parent' = q := by
    intro q l' k hk hkn hpq
    obtain ⟨-, r0, hr0, -⟩ := c5 k l' hk
    have hl'n : l' ≠ nl := by intro he; rw [he] at hk; exact hkn (hinj _ _ _ hk hnm1)
    obtain ⟨r0', h1, h2', -, -, -⟩ := hold l' r0 hr0 hl'n
    exact ⟨r0', h1, by rw [h2']; exact hpq r0 hr0⟩
  refine ⟨c1, c2, fun h0 => absurd h0 hrn, fun _ => ?_, ?_, c6, fun h0 => absurd h0 hroot0, ?_, ?_, ?_⟩
  · -- the root is cached
    have h4 := c4 hrn
    show (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)).nm !! B.ib.root' = some B.bv.rootNode'
    rw [hnm', if_neg]; exact h4
    intro he; rw [he] at h4; exact hroot (Option.some.inj (h4.symm.trans hnm1))
  · intro c l hl
    rw [hnm'] at hl
    split at hl
    · cases hl
    rename_i hcn
    obtain ⟨hnn, r0, hr0, hp0⟩ := c5 c l hl
    have hln : l ≠ nl := by intro he; rw [he] at hl; exact hcn (hinj _ _ _ hl hnm1)
    obtain ⟨r0', h1, -, -, h4, -⟩ := hold l r0 hr0 hln
    exact ⟨hnn, r0', h1, by rw [h4]; exact hp0⟩
  · intro y ry' hy
    rw [hns'] at hy
    split at hy
    · rename_i hyp
      cases hy; subst y
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := hnp
      refine ⟨n1, ?_, wsSorted_eraseIdx _ _ n3, fun x hx => n4 x (List.mem_of_mem_eraseIdx hx),
        fun x hx => n5 x (List.mem_of_mem_eraseIdx hx), n6, ?_, n8, n9, n10, fun h => ?_,
        fun _ => ?_, n13, fun hp => ?_, ?_, ?_⟩
      · show (rp.ins.eraseIdx i).length = (rp.ws.eraseIdx i).length
        rw [List.length_eraseIdx_of_lt (by omega), List.length_eraseIdx_of_lt hil, hilen]
      · show (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)).nm !! rp.nv.pgid' = some pl
        rw [hnm', if_neg hpg]; exact n7
      · exact absurd (h.symm.trans hbr) (by nofun)
      · obtain ⟨-, -, hk⟩ := n12 hbr
        refine ⟨by show 0 < (rp.ws.eraseIdx i).length; rw [List.length_eraseIdx_of_lt hil]; omega,
          (hnd.sublist ((List.eraseIdx_sublist _ _).map _)), fun x hx => ?_⟩
        obtain ⟨hxm, hxn⟩ := hmem' x hx
        obtain ⟨k1, k2, k3⟩ := hk x hxm
        refine ⟨k1, fun l' hl' => ?_, fun hn => ?_⟩
        · rw [hnm', if_neg hxn] at hl'
          exact hchild pl l' x.pgid hl' hxn (fun r' hr' => by
            obtain ⟨r'', h1, h2⟩ := k2 l' hl'; rw [hr'] at h1; cases h1; exact h2)
        · rw [hnm', if_neg hxn] at hn; exact k3 hn
      · obtain ⟨rq, hrq, hbq, hiq, x, hx, hxp⟩ := n14 hp
        have hqn : rp.nv.parent' ≠ nl := hnotp pl rp hrp
        obtain ⟨rq', h1, -, h3, -, h5⟩ := hold _ rq hrq hqn
        have hqy : rp.nv.parent' ≠ pl := hnself
        rw [h5 hqy] at h1
        exact ⟨rq, h1, hbq, hiq, x, hx, hxp⟩
      · show (rp.cs.eraseIdx (rp.cs.idxOf nl)).Nodup
        rw [cs_erase]; exact n15.erase _
      · intro c hcin
        obtain ⟨hcn, hcm⟩ := (hcs' c).1 hcin
        obtain ⟨rc, hrc, hpc⟩ := n16 c hcm
        obtain ⟨rc', h1, h2', -, -, -⟩ := hold c rc hrc hcn
        exact ⟨rc', h1, by rw [h2']; exact hpc⟩
    · rename_i hyp
      split at hy
      · cases hy
      rename_i hyn
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := c8 y ry' hy
      have hpgy : ry'.nv.pgid' ≠ r.nv.pgid' := by
        intro he; rw [he] at n7; exact hyn (Option.some.inj (n7.symm.trans hnm1))
      refine ⟨n1, n2, n3, n4, n5, n6, by rw [hnm', if_neg hpgy]; exact n7, n8, n9, n10, n11, ?_, n13,
        fun hp => ?_, n15, ?_⟩
      · intro hb
        obtain ⟨a1, a2, hk⟩ := n12 hb
        refine ⟨a1, a2, fun x hx => ?_⟩
        obtain ⟨k1, k2, k3⟩ := hk x hx
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
        have hxn : x.pgid ≠ r.nv.pgid' := fun he => hyp (honly y ry' j x hy hb hj he).1
        refine ⟨k1, fun l' hl' => ?_, fun hn => ?_⟩
        · rw [hnm', if_neg hxn] at hl'
          exact hchild y l' x.pgid hl' hxn (fun r' hr' => by
            obtain ⟨r'', h1, h2⟩ := k2 l' hl'; rw [hr'] at h1; cases h1; exact h2)
        · rw [hnm', if_neg hxn] at hn; exact k3 hn
      · obtain ⟨rq, hrq, hbq, hiq, x, hx, hxp⟩ := n14 hp
        have hqn : ry'.nv.parent' ≠ nl := hnotp y ry' hy
        obtain ⟨rq', h1, -, h3, -, h5⟩ := hold _ rq hrq hqn
        by_cases hqp : ry'.nv.parent' = pl
        · rw [hqp, hrp] at hrq; cases hrq
          rw [hqp, hns', if_pos rfl] at h1
          refine ⟨_, by rw [hqp, hns', if_pos rfl], by show rp.nv.isLeaf' = false; exact hbr,
            (hcs' y).2 ⟨hyn, hiq⟩, x, hmemw x hx (by rw [hxp]; exact hpgy), hxp⟩
        · rw [h5 hqp] at h1
          exact ⟨rq, h1, hbq, hiq, x, hx, hxp⟩
      · intro c hcin
        obtain ⟨rc, hrc, hpc⟩ := n16 c hcin
        have hcn : c ≠ nl := by intro he; rw [he, hr] at hrc; cases hrc; rw [hpl] at hpc; exact hyp hpc.symm
        obtain ⟨rc', h1, h2', -, -, -⟩ := hold c rc hrc hcn
        exact ⟨rc', h1, by rw [h2']; exact hpc⟩
  · -- page positions: those of the old bucket
    intro l1 i1 q1 l2 i2 q2 h1 h2' hne d hd
    refine c9 _ _ q1 _ _ q2 (hpos _ _ _ h1) (hpos _ _ _ h2') ?_ d hd
    intro he; apply hne
    simp only [Prod.mk.injEq] at he ⊢
    obtain ⟨rfl, he2⟩ := he
    refine ⟨rfl, ?_⟩
    by_cases hlp : l1 = pl
    · rw [if_pos hlp, if_pos hlp] at he2
      split at he2 <;> split at he2 <;> omega
    · rw [if_neg hlp, if_neg hlp] at he2; exact he2
  · intro l j q hp d hd
    have := c10 _ _ q (hpos _ _ _ hp) d hd
    rw [hnm']; split
    · rfl
    · exact this

include hroot hnself in
theorem rm_keys (h2 : 2 ≤ rp.ws.length) (bnd : Loc → Option (List w8) × Option (List w8))
    (hk : rblKeysB W B bnd (some nl)) :
    rblKeysB W (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC))
      (fun x => if x = pl ∧ i = 0 then (some (wKey rp.ws 1), (bnd pl).2) else bnd x) (some pl) := by
  obtain ⟨hbr, hin, hnlpl, hnm1, hnm2, hpg, hnotp, honly, hnd, hroot0⟩ :=
    rm_basic W hwm bl B nl r pl rp i w hc hr hleaf hpl hpn hrp hw hwp
  have hold := rm_old W hwm bl B nl r pl rp i w sI sC hc hr hleaf hpl hpn hrp hw hwp h2
  have hnm' := rm_nm B nl pl r.nv.pgid' (rmParent rp i nl sI sC)
  have hns' := rm_ns B nl pl r.nv.pgid' (rmParent rp i nl sI sC)
  have hinj := nm_inj W hwm bl B hc
  have hil : i < rp.ws.length := (List.getElem?_eq_some_iff.1 hw).1
  have hnp := hc.2.2.2.2.2.2.2.1 pl rp hrp
  obtain ⟨k1, k2, k3⟩ := hk
  have hbpl : (fun x => if x = pl ∧ i = 0 then (some (wKey rp.ws 1), (bnd pl).2) else bnd x) pl =
      if i = 0 then (some (wKey rp.ws 1), (bnd pl).2) else bnd pl := by
    by_cases hi0 : i = 0 <;> simp [hi0]
  have hbne : ∀ x, x ≠ pl → (fun x => if x = pl ∧ i = 0 then (some (wKey rp.ws 1), (bnd pl).2) else bnd x) x = bnd x := by
    intro x hx; simp [hx]
  obtain ⟨p1, -, p3, -, -⟩ := k3 pl rp hrp
  obtain ⟨-, pfst, kind, pkd⟩ := p3 hbr
  have hsorted : wsSorted rp.ws := hnp.2.2.1
  -- the entries of the parent, kept
  have hpos : ∀ j' x, rp.ws[j']? = some x → x.pgid ≠ r.nv.pgid' →
      j' ≠ i ∧ (rp.ws.eraseIdx i)[if j' < i then j' else j' - 1]? = some x := by
    intro j' x hx hxn
    have hji : j' ≠ i := by intro he; subst he; rw [hw] at hx; cases hx; exact hxn hwp
    refine ⟨hji, ?_⟩
    rw [getElem?_eraseIdx']
    have : (if (if j' < i then j' else j' - 1) < i then (if j' < i then j' else j' - 1)
        else (if j' < i then j' else j' - 1) + 1) = j' := by
      by_cases h : j' < i
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg (by omega)]; omega
    rw [this]; exact hx
  have hback : ∀ j x, (rp.ws.eraseIdx i)[j]? = some x →
      ∃ j', rp.ws[j']? = some x ∧ j' ≠ i ∧ j = (if j' < i then j' else j' - 1) := by
    intro j x hx
    rw [getElem?_eraseIdx'] at hx
    by_cases h : j < i
    · rw [if_pos h] at hx; exact ⟨j, hx, by omega, by rw [if_pos h]⟩
    · rw [if_neg h] at hx; exact ⟨j + 1, hx, by omega, by rw [if_neg (by omega)]; omega⟩
  have hbndpl : bndIn ((fun x => if x = pl ∧ i = 0 then (some (wKey rp.ws 1), (bnd pl).2) else bnd x) pl)
      (bnd pl) := by
    rw [hbpl]
    by_cases hi0 : i = 0
    · rw [if_pos hi0]
      refine bndIn_lo _ (fun y hy => ⟨_, rfl, ?_⟩)
      have h0 := p1 (rp.ws[0]'(by omega)) (List.getElem_mem _)
      have hl := hsorted 0 1 (by omega) (by omega)
      rw [wKey_get rp.ws 0 (by omega)] at hl
      exact rk_le_of_lt (rk_lt_of_le_lt (h0.1 y hy) hl)
    · rw [if_neg hi0]; exact bndIn_refl _
  refine ⟨k1, fun r0 h0 => ?_, fun y ry' hy => ?_⟩
  · change (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)).ns !! B.bv.rootNode' = some r0 at h0
    rw [hns'] at h0
    split at h0
    · rename_i he
      cases h0
      exact k2 rp (by rw [he]; exact hrp)
    all_goals first | exact k2 r0 h0 | cases h0 | (rw [if_neg hroot] at h0; exact k2 r0 h0)
  rw [hns'] at hy
  split at hy
  · -- the parent
    rename_i hyp
    cases hy; subst y
    refine ⟨fun x hx => ?_, fun hp => ?_, fun _ => ⟨fun h => absurd rfl h, fun x hx => ?_, kind, ?_⟩,
      fun h => absurd rfl h, fun h => absurd h (by show ¬ (rp.nv.isLeaf' = true); rw [hbr]; nofun)⟩
    · -- its keys
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
      obtain ⟨j', hj', hji, rfl⟩ := hback j x hj
      rw [hbpl]
      by_cases hi0 : i = 0
      · rw [if_pos hi0]
        have hxk := p1 x (List.mem_of_getElem? hj')
        refine ⟨fun y hy => ?_, hxk.2⟩
        cases hy
        have hjl := (List.getElem?_eq_some_iff.1 hj').1
        have h1 : 1 ≤ j' := by omega
        rcases Nat.lt_or_ge 1 j' with h | h
        · have := hsorted 1 j' h hjl
          rw [wKey_get rp.ws j' hjl, show rp.ws[j'] = x from (List.getElem?_eq_some_iff.1 hj').2] at this
          exact rk_le_of_lt this
        · have : j' = 1 := by omega
          subst this
          rw [wKey_get rp.ws 1 hjl, show rp.ws[1] = x from (List.getElem?_eq_some_iff.1 hj').2]
          exact rk_le_refl _
      · rw [if_neg hi0]; exact p1 x (List.mem_of_getElem? hj')
    · -- its position
      obtain ⟨hkey, rq, j, x, hrq, hx, hxp, hxk, hbn⟩ := (k3 pl rp hrp).2.1 hp
      have hqn : rp.nv.parent' ≠ nl := hnotp pl rp hrp
      obtain ⟨rq', h1, -, -, -, h5⟩ := hold _ rq hrq hqn
      refine ⟨hkey, rq, j, x, ?_, hx, hxp, hxk, ?_⟩
      · rw [← h5 hnself]; exact h1
      · show bndIn ((fun x => if x = pl ∧ i = 0 then (some (wKey rp.ws 1), (bnd pl).2) else bnd x) pl)
          (entryBnd ((fun x => if x = pl ∧ i = 0 then (some (wKey rp.ws 1), (bnd pl).2) else bnd x)
            rp.nv.parent') rq.ws j)
        rw [hbne _ hnself]; exact bndIn_trans hbndpl hbn
    · -- its first key
      rw [hbpl] at hx
      by_cases hi0 : i = 0
      · rw [if_pos hi0] at hx; cases hx
        show wKey (rp.ws.eraseIdx i) 0 = wKey rp.ws 1
        unfold wKey; rw [getElem?_eraseIdx', if_neg (by omega)]
      · rw [if_neg hi0] at hx
        show wKey (rp.ws.eraseIdx i) 0 = x
        unfold wKey; rw [getElem?_eraseIdx', if_pos (by omega)]
        exact pfst x hx
    · -- its children
      intro j x hx
      obtain ⟨j', hj', hji, rfl⟩ := hback j x hx
      have hxn : x.pgid ≠ r.nv.pgid' := by
        intro he; exact hji (honly pl rp j' x hrp hbr hj' he).2
      obtain ⟨a1, a2⟩ := pkd j' x hj'
      refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
      · rw [hnm', if_neg hxn] at hl'
        obtain ⟨r0, hr0, hk0⟩ := a1 l' hl'
        have hl'n : l' ≠ nl := by intro he; rw [he] at hl'; exact hxn (hinj _ _ _ hl' hnm1)
        obtain ⟨r0', h1, -, h3, -, -⟩ := hold l' r0 hr0 hl'n
        exact ⟨r0', h1, by rw [h3]; exact hk0⟩
      · rw [hnm', if_neg hxn] at hn
        obtain ⟨pg, b1, b2, b3, b4, b5⟩ := a2 hn
        refine ⟨pg, b1, b2, b3, b4, ?_⟩
        have hb := entryBnd_erase rp.ws i (bnd pl) hsorted p1 h2 hil j'
          (List.getElem?_eq_some_iff.1 hj').1 hji
        rw [← hbpl] at hb
        exact treeKeys_mono W.pages _ _ _ b5 _ _ hb
  · rename_i hyp
    split at hy
    · cases hy
    rename_i hyn
    obtain ⟨n1, n2, n3, n4, n5⟩ := k3 y ry' hy
    refine ⟨by rw [hbne _ hyp]; exact n1, fun hp => ?_, fun hb => ?_,
      fun _ => n4 (by intro he; cases he; exact hyn rfl), n5⟩
    · obtain ⟨hkey, rq, j, x, hrq, hx, hxp, hxk, hbn⟩ := n2 hp
      have hqn : ry'.nv.parent' ≠ nl := hnotp y ry' hy
      have hxn : x.pgid ≠ r.nv.pgid' := by
        intro he; rw [hxp] at he
        have := hc.2.2.2.2.2.2.2.1 y ry' hy
        exact hyn (Option.some.inj (this.2.2.2.2.2.2.1.symm.trans (he ▸ hnm1)))
      by_cases hqp : ry'.nv.parent' = pl
      · rw [hqp, hrp] at hrq; cases hrq
        obtain ⟨hji, hx'⟩ := hpos j x hx hxn
        refine ⟨hkey, rmParent rp i nl sI sC, _, x, by rw [hqp, hns', if_pos rfl], hx', hxp, hxk, ?_⟩
        rw [hbne _ hyp, hqp]
        have hb := entryBnd_erase rp.ws i (bnd pl) hsorted p1 h2 hil j
          (List.getElem?_eq_some_iff.1 hx).1 hji
        rw [← hbpl] at hb
        rw [hqp] at hbn
        exact bndIn_trans hbn hb
      · obtain ⟨rq', h1, -, -, -, h5⟩ := hold _ rq hrq hqn
        rw [h5 hqp] at h1
        exact ⟨hkey, rq, j, x, h1, hx, hxp, hxk, by rw [hbne _ hyp, hbne _ hqp]; exact hbn⟩
    · obtain ⟨a1, a2, kind', a3⟩ := n3 hb
      refine ⟨fun hd => a1 (by intro he; cases he; exact hyn rfl), by rw [hbne _ hyp]; exact a2,
        kind', fun j x hx => ?_⟩
      obtain ⟨b1, b2⟩ := a3 j x hx
      have hxn : x.pgid ≠ r.nv.pgid' := fun he => hyp (honly y ry' j x hy hb hx he).1
      refine ⟨fun l' hl' => ?_, fun hn => ?_⟩
      · rw [hnm', if_neg hxn] at hl'
        obtain ⟨r0, hr0, hk0⟩ := b1 l' hl'
        have hl'n : l' ≠ nl := by intro he; rw [he] at hl'; exact hxn (hinj _ _ _ hl' hnm1)
        obtain ⟨r0', h1, -, h3, -, -⟩ := hold l' r0 hr0 hl'n
        exact ⟨r0', h1, by rw [h3]; exact hk0⟩
      · rw [hnm', if_neg hxn] at hn
        rw [hbne _ hyp]; exact b2 hn

theorem rm_ht (hh : rblHt W B) : rblHt W (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)) := by
  obtain ⟨hbr, hin, hnlpl, hnm1, hnm2, hpg, hnotp, honly, hnd, hroot0⟩ :=
    rm_basic W hwm bl B nl r pl rp i w hc hr hleaf hpl hpn hrp hw hwp
  obtain ⟨ht, pht, hp, hh⟩ := hh
  refine ⟨ht, pht, hp, fun y ry' hy => ?_⟩
  rw [rm_ns] at hy
  have hent : ∀ y ry, B.ns !! y = some ry → ry.nv.isLeaf' = false → ∀ x ∈ ry.ws, x.pgid ≠ r.nv.pgid' →
      (∀ l', (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)).nm !! x.pgid = some l' → ht l' + 1 = ht y) ∧
      ((rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)).nm !! x.pgid = none →
        pht (uint.nat x.pgid) + 1 = ht y) := by
    intro y ry hy hb x hx hxn
    obtain ⟨a1, a2⟩ := (hh y ry hy).2 hb x hx
    rw [rm_nm, if_neg hxn]
    exact ⟨a1, a2⟩
  split at hy
  · rename_i hyp
    cases hy; subst y
    refine ⟨fun h => absurd h (by show ¬ (rp.nv.isLeaf' = true); rw [hbr]; nofun), fun _ x hx => ?_⟩
    obtain ⟨j, hji, hj⟩ := List.mem_eraseIdx_iff_getElem?.1 hx
    exact hent pl rp hrp hbr x (List.mem_of_getElem? hj) (fun he => hji (honly pl rp j x hrp hbr hj he).2)
  · rename_i hyp
    split at hy
    · cases hy
    · refine ⟨(hh y ry' hy).1, fun hb x hx => ?_⟩
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
      exact hent y ry' hy hb x hx (fun he => hyp (honly y ry' j x hy hb hj he).1)

theorem rm_acyc (h2 : 2 ≤ rp.ws.length) (ha : rblAcyc B) :
    rblAcyc (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)) := by
  obtain ⟨ht, hh⟩ := ha
  refine ⟨ht, fun y ry' hy hp => ?_⟩
  rw [rm_ns] at hy
  split at hy
  · rename_i hyp; cases hy; subst y; exact hh pl rp hrp hp
  · split at hy
    · cases hy
    · exact hh y ry' hy hp

theorem rm_unbal (y : Loc) (ry' : NRec)
    (hy : (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)).ns !! y = some ry') :
    y = pl ∨ (y ≠ nl ∧ B.ns !! y = some ry') := by
  rw [rm_ns] at hy
  split at hy
  · rename_i hyp; exact Or.inl hyp
  · split at hy
    · cases hy
    · rename_i _ hyn; exact Or.inr ⟨hyn, hy⟩

include hemp in
theorem rm_entryIn (k v : List w8) (h : entryIn W B k v) :
    entryIn W (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)) k v := by
  obtain ⟨hbr, hin, hnlpl, hnm1, hnm2, hpg, hnotp, honly, hnd, hroot0⟩ :=
    rm_basic W hwm bl B nl r pl rp i w hc hr hleaf hpl hpn hrp hw hwp
  rcases h with ⟨y, ry, x, hy, hl, hx, hk, hbk, hv⟩ | ⟨c, q, pgq, j, hpos, ho, hpq, hlq, hj, hkq, hfq, hvq⟩
  · have hyn : y ≠ nl := by intro he; rw [he, hr] at hy; cases hy; rw [hemp] at hx; cases hx
    have hyp : y ≠ pl := by intro he; rw [he, hrp] at hy; cases hy; rw [hbr] at hl; cases hl
    refine Or.inl ⟨y, ry, x, ?_, hl, hx, hk, hbk, hv⟩
    rw [rm_ns, if_neg hyp, if_neg hyn]; exact hy
  · refine Or.inr ⟨c, q, pgq, j, ?_, ho, hpq, hlq, hj, hkq, hfq, hvq⟩
    unfold posRoot at hpos ⊢
    rcases hpos with h1 | ⟨y, j0, ⟨ry, x, hy, hyb, hx, hxc, hn⟩, hlt⟩
    · exact Or.inl h1
    · right
      have hxn : x.pgid ≠ r.nv.pgid' := by intro he; rw [hxc] at he; rw [he, hnm1] at hn; cases hn
      have hn' : (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)).nm !! W64 (c : Int) = none := by
        rw [rm_nm, if_neg (by rw [← hxc]; exact hxn)]; exact hn
      have hyn : y ≠ nl := by intro he; rw [he, hr] at hy; cases hy; rw [hleaf] at hyb; cases hyb
      by_cases hyp : y = pl
      · subst y
        rw [hrp] at hy; cases hy
        have hji : j0 ≠ i := by intro he; subst he; rw [hw] at hx; cases hx; exact hxn hwp
        refine ⟨pl, if j0 < i then j0 else j0 - 1, ⟨rmParent rp i nl sI sC, x, by rw [rm_ns, if_pos rfl], hyb, ?_,
          hxc, hn'⟩, hlt⟩
        show (rp.ws.eraseIdx i)[if j0 < i then j0 else j0 - 1]? = some x
        rw [getElem?_eraseIdx']
        have : (if (if j0 < i then j0 else j0 - 1) < i then (if j0 < i then j0 else j0 - 1)
            else (if j0 < i then j0 else j0 - 1) + 1) = j0 := by
          by_cases h : j0 < i
          · rw [if_pos h, if_pos h]
          · rw [if_neg h, if_neg (by omega)]; omega
        rw [this]; exact hx
      · exact ⟨y, j0, ⟨ry, x, by rw [rm_ns, if_neg hyp, if_neg hyn]; exact hy, hyb, hx, hxc, hn'⟩, hlt⟩

end rm

end pure

section comb
variable [ext : FfiSyntax]

/-- A search for a key of sorted entries finds it. -/
theorem searchIdx_eq (es : List NodeEntry) (hs : entriesSorted es) (kb : List w8) (j : Nat)
    (hj : j < es.length) (hk : entryKey es j = kb) (idx : Nat) (h : isSearchIdx es kb idx) :
    idx = j := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases Nat.lt_trichotomy idx j with hlt | heq | hgt
  · have := hs idx j hlt hj
    rw [hk] at this
    exact absurd this (h3 (by omega))
  · exact heq
  · have := h2 j hgt
    rw [hk] at this
    exact absurd this (goStringLt_irrefl_w kb)

/-- An empty leaf (`nl`, the deficient node, no longer marked unbalanced) removed from its
parent `pl` (entry `i`): the bucket in the invariant, the parent the deficient node. -/
theorem rbl_rm (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (nl : Loc) (r : NRec) (pl : Loc)
    (rp : NRec) (i : Nat) (w : WEntry) (sI sC : GoSlice)
    (HB : rblB W hwm bl B (some nl)) (hr : B.ns !! nl = some r) (hleaf : r.nv.isLeaf' = true)
    (hemp : r.ws = []) (hpl : r.nv.parent' = pl) (hpn : pl ≠ null) (hrp : B.ns !! pl = some rp)
    (hw : rp.ws[i]? = some w) (hwp : w.pgid = r.nv.pgid') :
    rblB W hwm bl (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)) (some pl) ∧
      (∀ k v, entryIn W B k v → entryIn W (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)) k v) ∧
      (∀ y ry', (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)).ns !! y = some ry' →
        y = pl ∨ (y ≠ nl ∧ B.ns !! y = some ry')) ∧
      (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)).ns !! pl = some (rmParent rp i nl sI sC) ∧
      2 ≤ rp.ws.length := by
  obtain ⟨hc, ⟨bnd, hk⟩, ha, hht⟩ := HB
  have hroot : B.bv.rootNode' ≠ nl := by
    intro he
    have := hk.2.1 r (by rw [he]; exact hr)
    rw [hpl] at this; exact hpn this
  have hnself : rp.nv.parent' ≠ pl := by
    intro he
    obtain ⟨ht, hh⟩ := ha
    have := hh pl rp hrp (by rw [he]; exact hpn)
    rw [he] at this; omega
  obtain ⟨hbr, -⟩ := rm_basic W hwm bl B nl r pl rp i w hc hr hleaf hpl hpn hrp hw hwp
  have hnlpl := (rm_basic W hwm bl B nl r pl rp i w hc hr hleaf hpl hpn hrp hw hwp).2.2.1
  have h2 : 2 ≤ rp.ws.length := ((hk.2.2 pl rp hrp).2.2.1 hbr).1 (fun he =>
    hnlpl (Option.some.inj he))
  refine ⟨⟨rm_clean W hwm bl B nl r pl rp i w sI sC hc hr hleaf hpl hpn hrp hw hwp hroot hnself h2,
      ⟨_, rm_keys W hwm bl B nl r pl rp i w sI sC hc hr hleaf hpl hpn hrp hw hwp hroot hnself h2 bnd hk⟩,
      rm_acyc W hwm bl B nl r pl rp i w sI sC hc hr hleaf hpl hpn hrp hw hwp h2 ha,
      rm_ht W hwm bl B nl r pl rp i w sI sC hc hr hleaf hpl hpn hrp hw hwp hht⟩,
    rm_entryIn W hwm bl B nl r pl rp i w sI sC hc hr hleaf hemp hpl hpn hrp hw hwp,
    rm_unbal W hwm bl B nl r pl rp i w sI sC hc hr hleaf hpl hpn hrp hw hwp,
    by rw [rm_ns, if_pos rfl], h2⟩

/-- Before the parent's rebalance: no field but the nodes changed, and the unbalanced nodes are
the parent and some of those before (not the node). -/
def rblPre (B B1 : BRec) (nl pl : Loc) : Prop :=
  B1.bv = B.bv ∧ B1.ib = B.ib ∧ B1.bm = B.bm ∧
  ∀ y ry', B1.ns !! y = some ry' → ry'.nv.unbalanced' = true →
    y = pl ∨ (y ≠ nl ∧ ∃ ry, B.ns !! y = some ry ∧ ry.nv.unbalanced' = true ∧ ry'.nv.pgid' = ry.nv.pgid')

theorem rblStep_comp (B B1 B2 : BRec) (nl pl : Loc) (h1 : rblPre B B1 nl pl) (h2 : rblStep B1 B2 pl) :
    rblStep B B2 nl := by
  obtain ⟨a1, a2, a3, a4⟩ := h1
  obtain ⟨b1, b2, b3, b4⟩ := h2
  refine ⟨b1.trans a1, b2.trans a2, b3.trans a3, fun y ry2 hy hu => ?_⟩
  obtain ⟨hyp, ry1, hy1, hu1, hp1⟩ := b4 y ry2 hy hu
  rcases a4 y ry1 hy1 hu1 with h | ⟨hyn, ry, hy0, hu0, hp0⟩
  · exact absurd h hyp
  · exact ⟨hyn, ry, hy0, hu0, hp1.trans hp0⟩

theorem rblPre_rm (B : BRec) (nl : Loc) (r : NRec) (pl : Loc) (rp' : NRec) :
    rblPre B (rmBkt (rblStart B nl r) nl pl r.nv.pgid' rp') nl pl := by
  refine ⟨rfl, rfl, rfl, fun y ry' hy hu => ?_⟩
  rw [rm_ns] at hy
  split at hy
  · rename_i h; exact Or.inl h
  · split at hy
    · cases hy
    · rename_i _ hyn
      change (<[nl := rblClear r]> B.ns) !! y = some ry' at hy
      rw [rf_lookup, if_neg hyn] at hy
      exact Or.inr ⟨hyn, ry', hy, hu, rfl⟩

end comb

section toks
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

theorem bigSepL_erase_mono {A : Type} (Φ Ψ : A → IProp GF) (l : List A) (i : Nat)
    (h : ∀ x ∈ l.eraseIdx i, Φ x ⊢ Ψ x) :
    ([∗list] x ∈ l, Φ x) ⊢ [∗list] x ∈ l.eraseIdx i, Ψ x := by
  have hmono : ([∗list] x ∈ l.eraseIdx i, Φ x) ⊢ [∗list] x ∈ l.eraseIdx i, Ψ x :=
    BigSepL.bigSepL_mono fun {_ x} hx => h x (List.mem_of_getElem? hx)
  refine BIBase.Entails.trans ?_ hmono
  rw [List.eraseIdx_eq_take_drop_succ]
  by_cases hi : i < l.length
  · conv => lhs; rw [← List.take_append_drop i l, List.drop_eq_getElem_cons hi]
    refine (BigSepL.bigSepL_append).1.trans ((sep_mono .rfl ?_).trans (BigSepL.bigSepL_append).2)
    exact (BigSepL.bigSepL_cons).1.trans (sep_elim_right)
  · rw [List.drop_of_length_le (by omega), List.append_nil, List.take_of_length_le (by omega)]

/-- A node's tokens after one of its entries is removed (the others' children unchanged). -/
theorem nodeToks_erase (γ : GName) (W : WView) (B B' : BRec) (rp rp' : NRec) (i : Nat)
    (hbm : B'.bm = B.bm) (hp : rp'.nv.pgid' = rp.nv.pgid') (hws : rp'.ws = rp.ws.eraseIdx i)
    (hl : rp'.nv.isLeaf' = rp.nv.isLeaf')
    (hnm : rp.nv.isLeaf' = false → ∀ x ∈ rp.ws.eraseIdx i, B'.nm !! x.pgid = B.nm !! x.pgid) :
    nodeToks (GF := GF) γ W B rp ⊢ nodeToks γ W B' rp' := by
  unfold nodeToks
  rw [hp, hws, hl, opened_eq B B' hbm]
  refine sep_mono .rfl (bigSepL_erase_mono _ _ _ _ fun x hx => ?_)
  by_cases hlf : rp.nv.isLeaf' = true
  · simp only [hlf, ↓reduceIte]; exact .rfl
  · have hf : rp.nv.isLeaf' = false := by simpa using hlf
    rw [if_neg hlf, if_neg hlf, hnm hf x hx]

variable (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (nl : Loc) (r : NRec) (pl : Loc) (rp : NRec)
  (i : Nat) (w : WEntry) (sI sC : GoSlice)
  (hc : bktClean W hwm bl B) (hr : B.ns !! nl = some r) (hleaf : r.nv.isLeaf' = true)
  (hemp : r.ws = []) (hpl : r.nv.parent' = pl) (hpn : pl ≠ null) (hrp : B.ns !! pl = some rp)
  (hw : rp.ws[i]? = some w) (hwp : w.pgid = r.nv.pgid')
include hc hr hleaf hemp hpl hpn hrp hw hwp

open Classical Iris.ProofMode in
/-- The tokens after the removal, and the leaf's page token. -/
theorem rm_toks (γ : GName) :
    bktToks (GF := GF) γ W B ⊢ bktToks γ W (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)) ∗
      (if r.nv.pgid' = W64 0 then emp else
        pgToks γ (GMap.filter (fun id _ => decide (id = uint.nat r.nv.pgid')) W.pages)) := by
  obtain ⟨hbr, hin, hnlpl, hnm1, hnm2, hpg, hnotp, honly, hnd, hroot0⟩ :=
    rm_basic W hwm bl B nl r pl rp i w hc hr hleaf hpl hpn hrp hw hwp
  have hrn : B.bv.rootNode' ≠ null := by
    intro h0; have := (hc.2.2.1 h0).1; rw [this] at hr; cases hr
  have hnm' := rm_nm B nl pl r.nv.pgid' (rmParent rp i nl sI sC)
  unfold bktToks
  rw [if_neg hrn]
  show _ ⊢ (if B.bv.rootNode' = null then _ else _) ∗ _
  rw [if_neg hrn]
  have he : (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)).ns =
      Std.insert (Std.delete (Std.delete B.ns nl) pl) pl (rmParent rp i nl sI sC) := by
    show <[pl := rmParent rp i nl sI sC]> (GMap.delete nl B.ns) = _
    rw [Iris.Std.LawfulPartialMap.insert_delete]; rfl
  rw [he]
  have hrp' : Std.get? (Std.delete B.ns nl) pl = some rp := by
    show (GMap.delete nl B.ns) !! pl = _; rw [GMap.lookup_delete_ne _ hnlpl]; exact hrp
  iintro H
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r)
    (show Std.get? B.ns nl = some r from hr)).1 $$ H with ⟨Hn, H⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r)
    hrp').1 $$ H with ⟨Hp, H⟩
  ihave Hown : (if r.nv.pgid' = W64 0 then emp else
      pgToks γ (GMap.filter (fun id _ => decide (id = uint.nat r.nv.pgid')) W.pages)) $$ [Hn]
  · unfold nodeToks; icases Hn with ⟨H, -⟩; iexact H
  isplitr [Hown]
  · iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun _ x => nodeToks (GF := GF) γ W
      (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)) x) (Iris.Std.get?_delete_eq rfl)).2
    isplitl [Hp]
    · iapply nodeToks_erase γ W B (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)) rp (rmParent rp i nl sI sC) i rfl rfl rfl rfl ?_ $$ Hp
      intro _ x hx
      obtain ⟨j, hji, hj⟩ := List.mem_eraseIdx_iff_getElem?.1 hx
      have hxn : x.pgid ≠ r.nv.pgid' := fun he => hji (honly pl rp j x hrp hbr hj he).2
      rw [hnm', if_neg hxn]
    · iapply (BigSepM.bigSepM_mono (M := GMap Loc) (Φ := fun _ r => nodeToks (GF := GF) γ W B r)
        (Ψ := fun _ x => nodeToks (GF := GF) γ W (rmBkt B nl pl r.nv.pgid' (rmParent rp i nl sI sC)) x)
        ?_) $$ H
      intro y ry hy
      have hy' : B.ns !! y = some ry ∧ y ≠ pl ∧ y ≠ nl := by
        change (GMap.delete pl (GMap.delete nl B.ns)) !! y = some ry at hy
        by_cases h1 : y = pl
        · subst h1; rw [GMap.lookup_delete] at hy; cases hy
        rw [GMap.lookup_delete_ne _ (Ne.symm h1)] at hy
        by_cases h2 : y = nl
        · subst h2; rw [GMap.lookup_delete] at hy; cases hy
        rw [GMap.lookup_delete_ne _ (Ne.symm h2)] at hy
        exact ⟨hy, h1, h2⟩
      refine nodeToks_congr γ W B _ ry ry rfl rfl rfl rfl ?_
      intro hlf x hx
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
      have hxn : x.pgid ≠ r.nv.pgid' := fun he => hy'.2.1 (honly y ry j x hy'.1 hlf hj he).1
      rw [hnm', if_neg hxn]
  · iexact Hown

end toks

end bbolt
end EtcdGrove
end Perennial
