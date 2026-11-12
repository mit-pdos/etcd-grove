/-
The merge of two siblings (`RblMg1.lean`, `RblMg2.lean`): the merged bucket keeps its keys, the
merged node's bounds the join of the two siblings' (`mgBnd`), the parent the deficient node
(`mg_keys`). Ported from `old/bbolt/.../RebalanceMg.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblMg2

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rbl
variable [GooseExts]

section mg
variable (W : View) (hwm : Nat) (bl : Loc) (B : BRec) (pl : Loc) (rp : NRec) (k : Nat)
  (wl wr : WEntry) (ll lr : Loc) (rl rr : NRec)
  (hc : bktClean W hwm bl B) (ha : rblAcyc B) (hpn : pl ≠ null) (hrp : B.ns !! pl = some rp)
  (hbr : rp.nv.isLeaf' = false)
  (hwl : rp.ws[k]? = some wl) (hwr : rp.ws[k + 1]? = some wr)
  (hll : B.nm !! wl.pgid = some ll) (hlr : B.nm !! wr.pgid = some lr)
  (hrl : B.ns !! ll = some rl) (hrr : B.ns !! lr = some rr)
include hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr

theorem mg_keys (sI sC sI' sC' : GoSlice) (hkind : rl.nv.isLeaf' = rr.nv.isLeaf')
    (hleaf0 : rr.nv.isLeaf' = true → ∀ w ∈ rr.ws, B.nm !! w.pgid = none)
    (hroot : B.bv.rootNode' ≠ lr) (hht : rblHt W B)
    (bnd : Loc → Option (List w8) × Option (List w8)) (dfc : Option Loc)
    (hk : rblKeysB W B bnd dfc) (hdfc : dfc = some ll ∨ dfc = some lr)
    (hne : 0 < (rl.ws ++ rr.ws).length) :
    rblKeysB W (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
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
  have hnm' := mg_nm B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
    (mgLeft rl rr (kidsOf B rr.ws) sI sC)
  have hns' := mg_ns B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
    (mgLeft rl rr (kidsOf B rr.ws) sI sC)
  have hinj := nm_inj_mg W hwm bl B hc
  have hnmr : B.nm !! rr.nv.pgid' = some lr := by rw [hpgr]; exact hlr
  have hnmo : ∀ c, c ≠ rr.nv.pgid' → (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
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
  have hbll : mgBnd bnd pl ll rp rl k ll = ((if rl.nv.isLeaf' then (wEntryBnd (bnd pl) rp.ws k).1 else
      (bnd ll).1), (wEntryBnd (bnd pl) rp.ws (k + 1)).2) := by simp [mgBnd]
  obtain ⟨p1, p2, p3, -, -⟩ := k3 pl rp hrp
  obtain ⟨-, pfst, kindp, pkd⟩ := p3 hbr
  have hsorted : wsSorted rp.ws := (hc.2.2.2.2.2.2.2.1 pl rp hrp).2.2.2.1
  -- the parent's new entry bounds
  have hposk : wEntryBnd (bnd pl) (rp.ws.eraseIdx (k + 1)) k =
      ((wEntryBnd (bnd pl) rp.ws k).1, (wEntryBnd (bnd pl) rp.ws (k + 1)).2) := by
    have hlen : (rp.ws.eraseIdx (k + 1)).length = rp.ws.length - 1 := List.length_eraseIdx_of_lt hil
    have hwk : ∀ j, wKey (rp.ws.eraseIdx (k + 1)) j = wKey rp.ws (if j < k + 1 then j else j + 1) := by
      intro j; unfold wKey; rw [getElem?_eraseIdx_mg]
    simp only [wEntryBnd_mg]; unfold childLo childHi
    rw [hlen]
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · split
      · rfl
      · rw [hwk, if_pos (by omega)]
    · by_cases h : k + 1 < rp.ws.length - 1
      · rw [if_pos h, if_pos (by omega), hwk, if_neg (by omega)]
      · rw [if_neg h, if_neg (by omega)]
  have hwrlo : ∀ y, (wEntryBnd (bnd pl) rp.ws k).1 = some y → ¬ go.GoStringLt wr.key y := by
    intro y hy
    have h0 := p1 wr (List.mem_of_getElem? hwr)
    rw [wEntryBnd_mg] at hy; unfold childLo at hy
    simp only at hy
    split at hy
    · exact h0.1 y hy
    · cases hy
      have := hsorted k (k + 1) (by omega) hil
      have hk1 : wKey rp.ws (k + 1) = wr.key := by unfold wKey; rw [hwr]; rfl
      rw [hk1] at this; exact rk_le_of_lt this
  have hwrhi : ∀ y, (wEntryBnd (bnd pl) rp.ws (k + 1)).2 = some y → go.GoStringLt wr.key y := by
    intro y hy
    have h0 := p1 wr (List.mem_of_getElem? hwr)
    rw [wEntryBnd_mg] at hy; unfold childHi at hy
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
    fun hb => ((hc.2.2.2.2.2.2.2.1 ll rl hrl).2.2.2.2.2.2.2.2.2.2.2.2.1 hb).1
  have hrrne : rr.nv.isLeaf' = false → 0 < rr.ws.length :=
    fun hb => ((hc.2.2.2.2.2.2.2.1 lr rr hrr).2.2.2.2.2.2.2.2.2.2.2.2.1 hb).1
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
  have hhiL : ∀ y, (wEntryBnd (bnd pl) rp.ws (k + 1)).2 = some y → ∃ x, (bnd ll).2 = some x ∧
      ¬ go.GoStringLt y x := by
    intro y hy
    obtain ⟨xh, hxh, hxh'⟩ := hbl.2 _ e1
    exact ⟨xh, hxh, rk_le_of_lt (rk_lt_of_le_lt hxh' (hwrhi y hy))⟩
  have hloR : rr.nv.isLeaf' = false → ∃ x, (bnd lr).1 = some x ∧ ¬ go.GoStringLt x (wKey rr.ws 0) := by
    intro hb
    obtain ⟨yl, hyl, -⟩ := hbr'.1 _ e2
    exact ⟨yl, hyl, by rw [((r3 hb).2.1 yl hyl)]; exact rk_le_refl _⟩
  have hentL : rl.nv.isLeaf' = false → ∀ j, j < rl.ws.length →
      bndIn (wEntryBnd (bnd ll) rl.ws j) (wEntryBnd (mgBnd bnd pl ll rp rl k ll) (rl.ws ++ rr.ws) j) := by
    intro hb j hj
    rw [hbll, if_neg (by rw [hb]; nofun)]
    exact entryBnd_left (bnd ll) _ rl.ws rr.ws j hj rfl (hR0 (by rw [← hkind]; exact hb)) hhiL
  have hentR : rl.nv.isLeaf' = false → ∀ j, j < rr.ws.length →
      bndIn (wEntryBnd (bnd lr) rr.ws j)
        (wEntryBnd (mgBnd bnd pl ll rp rl k ll) (rl.ws ++ rr.ws) (rl.ws.length + j)) := by
    intro hb j hj
    rw [hbll]
    exact entryBnd_right (bnd lr) _ rl.ws rr.ws j hj (hrlne hb) (hloR (by rw [← hkind]; exact hb))
      hbr'.2
  -- the entries of the parent after the removal of the right one's
  have hback : ∀ j x, (rp.ws.eraseIdx (k + 1))[j]? = some x →
      ∃ j', rp.ws[j']? = some x ∧ j' ≠ k + 1 ∧ j = (if j' < k + 1 then j' else j' - 1) := by
    intro j x hx
    rw [getElem?_eraseIdx_mg] at hx
    by_cases h : j < k + 1
    · rw [if_pos h] at hx; exact ⟨j, hx, by omega, by rw [if_pos h]⟩
    · rw [if_neg h] at hx; exact ⟨j + 1, hx, by omega, by rw [if_neg (by omega)]; omega⟩
  have hpos : ∀ j' x, rp.ws[j']? = some x → j' ≠ k + 1 →
      (rp.ws.eraseIdx (k + 1))[if j' < k + 1 then j' else j' - 1]? = some x := by
    intro j' x hx hji
    rw [getElem?_eraseIdx_mg]
    have : (if (if j' < k + 1 then j' else j' - 1) < k + 1 then (if j' < k + 1 then j' else j' - 1)
        else (if j' < k + 1 then j' else j' - 1) + 1) = j' := by
      by_cases h : j' < k + 1
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg (by omega)]; omega
    rw [this]; exact hx
  have hentP : ∀ j', j' < rp.ws.length → j' ≠ k + 1 →
      bndIn (wEntryBnd (bnd pl) rp.ws j')
        (wEntryBnd (bnd pl) (rp.ws.eraseIdx (k + 1)) (if j' < k + 1 then j' else j' - 1)) := by
    intro j' hj' hji
    have := wEntryBnd_erase_mg rp.ws (k + 1) (bnd pl) hsorted p1 (by omega) hil j' hj' hji
    rwa [if_neg (by omega)] at this
  -- a child in the old bucket, its record in the new
  have hkidrec : ∀ (q : Loc) (x : WEntry) (l' : Loc), B.nm !! x.pgid = some l' → x.pgid ≠ rr.nv.pgid' →
      ∀ r0, B.ns !! l' = some r0 → ∃ r', (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns !! l' = some r' ∧ r'.nv.isLeaf' = r0.nv.isLeaf' := by
    intro q x l' hl' hxn r0 hr0
    have hl'r : l' ≠ lr := by intro he; rw [he] at hl'; exact hxn (hinj _ _ _ hl' hnmr)
    obtain ⟨r', h1, -, h3, -⟩ := hlook l' r0 hr0 hl'r
    exact ⟨r', h1, h3⟩
  refine ⟨k1, fun r0 h0 => ?_, fun y ry' hy => ?_⟩
  · -- the root
    change (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
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
      · show bndIn (mgBnd bnd pl ll rp rl k pl) (wEntryBnd (mgBnd bnd pl ll rp rl k rp.nv.parent') _ i)
        rw [hbne _ (Ne.symm hllp), hbne _ hql]
        split <;> exact hbn
    · rw [hbne _ (Ne.symm hllp)] at hx
      show wKey (rp.ws.eraseIdx (k + 1)) 0 = x
      unfold wKey; rw [getElem?_eraseIdx_mg, if_pos (by omega)]
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
        exact go.goStringLt_trans (kx.2 _ e1) (hwrhi y hy)
      · exact (keyIn_bndIn hbr' _ (r1 x h)).2 y hy
    refine ⟨fun x hx => ⟨hlo0 x hx, hhi0 x hx⟩, fun hp => ?_, fun hb => ?_, fun _ hlf hu hp => ?_,
      fun hlf x hx => ?_⟩
    · -- its position: the left one's entry, the right one's high bound
      obtain ⟨hkey, rq, i, x, hrq, hx, hxp, hxk, -⟩ := l2 (by rw [hp1]; exact hpn)
      rw [hp1, hrp] at hrq; cases hrq
      have hik : i = k := by
        by_cases h : i = k
        · exact h
        · exact absurd (by rw [hxp, hpgl]) (nodup_pgid_ne_mg rp.ws hnd k i wl x hwl hx h)
      subst hik
      refine ⟨hkey, mgParent rp (i + 1) lr sI' sC', i, x, by change _ !! rl.nv.parent' = _; rw [hp1, hns', if_pos rfl], ?_, hxp, hxk, ?_⟩
      · show (rp.ws.eraseIdx (i + 1))[i]? = some x
        rw [getElem?_eraseIdx_mg, if_pos (by omega)]; exact hx
      · show bndIn (mgBnd bnd pl ll rp rl i ll)
          (wEntryBnd (mgBnd bnd pl ll rp rl i rl.nv.parent') (rp.ws.eraseIdx (i + 1)) i)
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
    intro he; have h7 := hnc.2.2.2.2.2.2.2.1; rw [he] at h7; exact hyr (Option.some.inj (h7.symm.trans hnmr))
  have hgen : ∀ ry' : NRec, ry'.ws = ry.ws → ry'.key = ry.key → ry'.nv.isLeaf' = ry.nv.isLeaf' →
      ry'.nv.key' = ry.nv.key' → ry'.nv.pgid' = ry.nv.pgid' → ry'.nv.unbalanced' = ry.nv.unbalanced' →
      ry'.nv.parent' = (if ry.nv.parent' = lr then ll else ry.nv.parent') →
      rblNodeKeys W (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
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
          obtain ⟨rq', hrq', hbq, -⟩ := hnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp0
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
          refine ⟨mgParent rp (k + 1) lr sI' sC', if i < k + 1 then i else i - 1, x,
            by rw [hqp, hns', if_pos rfl], hpos i x hx hji, hxp, hxk, ?_⟩
          rw [hqp, hbne _ (Ne.symm hllp)]
          rw [hqp] at hbn
          exact bndIn_trans hbn (hentP i (List.getElem?_eq_some_iff.1 hx).1 hji)
        by_cases hql : ry.nv.parent' = ll
        · rw [hql, hrl] at hrq; cases hrq
          have hbl2 : rl.nv.isLeaf' = false := by
            obtain ⟨rq', hrq', hbq, -⟩ := hnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp0
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

end mg

end rbl

end bbolt
end EtcdGrove
end Perennial
