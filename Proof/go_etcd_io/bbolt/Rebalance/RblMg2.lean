/-
The merge of two siblings (`RblMg1.lean`): the basic facts of the siblings and their parent
(`mg_basic`, `mg_cyc`, `mg_only`), the moved children (`mg_moved`), the merged bucket's records
(`mg_other`, `mg_look`), its page positions (`mg_pos`) and the siblings' bounds (`mg_bnds`,
`mg_lt`). Ported from `old/bbolt/.../RebalanceMg.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblMg1

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

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

theorem mg_basic :
    rl.nv.parent' = pl ∧ rr.nv.parent' = pl ∧ ll ≠ lr ∧ ll ≠ pl ∧ lr ≠ pl ∧
      rl.nv.pgid' = wl.pgid ∧ rr.nv.pgid' = wr.pgid ∧ B.nm !! rp.nv.pgid' = some pl ∧
      (rp.ws.map WEntry.pgid).Nodup ∧ B.ib.root' ≠ W64 0 ∧ ll ∈ rp.cs ∧ lr ∈ rp.cs ∧
      (∀ y ry, B.ns !! y = some ry → ry.nv.parent' ≠ null → ry.nv.parent' ≠ y) ∧
      wl.pgid ≠ wr.pgid ∧ rp.nv.parent' ≠ pl := by
  have hnp := hc.2.2.2.2.2.2.2.1 pl rp hrp
  obtain ⟨-, hnd, hkids⟩ := hnp.2.2.2.2.2.2.2.2.2.2.2.2.1 hbr
  obtain ⟨r1, hr1, hp1⟩ := (hkids wl (List.mem_of_getElem? hwl)).2.1 ll hll
  rw [hrl] at hr1; cases hr1
  obtain ⟨r2, hr2, hp2⟩ := (hkids wr (List.mem_of_getElem? hwr)).2.1 lr hlr
  rw [hrr] at hr2; cases hr2
  have hpg : wl.pgid ≠ wr.pgid := nodup_pgid_ne_mg rp.ws hnd (k + 1) k wr wl hwr hwl (by omega)
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
    obtain ⟨rq, hrq, -, hiq, -⟩ := (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [hp]; exact hpn)
    rw [hp, hrp] at hrq; cases hrq; exact hiq
  have hroot0 : B.ib.root' ≠ W64 0 := by
    intro h0; have := hc.2.2.2.2.2.2.1 h0 pl rp hrp; rw [hbr] at this; cases this
  refine ⟨hp1, hp2, hllr, hllp, hlrp, hp3, hp4, hnp.2.2.2.2.2.2.2.1, hnd, hroot0, hin ll rl hrl hp1,
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
  obtain ⟨-, -, hk⟩ := (hc.2.2.2.2.2.2.2.1 y ry hy).2.2.2.2.2.2.2.2.2.2.2.2.1 hb
  obtain ⟨-, hs, -⟩ := hk x (List.mem_of_getElem? hj)
  rw [hx] at hs
  obtain ⟨r1, hr1, hpr⟩ := hs lr hlr
  rw [hrr] at hr1; cases hr1
  rw [hp2] at hpr; subst hpr
  rw [hrp] at hy; cases hy
  refine ⟨rfl, ?_⟩
  by_cases hji : j = k + 1
  · exact hji
  · exact absurd (by rw [hx]) (nodup_pgid_ne_mg rp.ws hnd (k + 1) j wr x hwr hj hji)

include hc in
theorem mg_moved (hleaf0 : rr.nv.isLeaf' = true → ∀ w ∈ rr.ws, B.nm !! w.pgid = none) :
    (∀ c, c ∈ kidsOf B rr.ws ↔ ∃ rc, B.ns !! c = some rc ∧ rc.nv.parent' = lr) ∧
      (kidsOf B rr.ws).Nodup := by
  have hnr := hc.2.2.2.2.2.2.2.1 lr rr hrr
  refine ⟨fun c => ⟨fun hcm => ?_, fun ⟨rc, hrc, hpc⟩ => ?_⟩, ?_⟩
  · obtain ⟨x, hx, hxc⟩ := List.mem_filterMap.1 hcm
    rcases (Bool.eq_false_or_eq_true rr.nv.isLeaf').symm with hb | hb
    · obtain ⟨-, -, hk⟩ := hnr.2.2.2.2.2.2.2.2.2.2.2.2.1 hb
      exact (hk x hx).2.1 c hxc
    · rw [hleaf0 hb x hx] at hxc; cases hxc
  · have hcn := hc.2.2.2.2.2.2.2.1 c rc hrc
    have hlrn : lr ≠ null := (hc.2.2.2.2.1 _ _ hlr).1
    obtain ⟨rq, hrq, -, -, x, hx, hxp⟩ := hcn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by rw [hpc]; exact hlrn)
    rw [hpc, hrr] at hrq; cases hrq
    exact List.mem_filterMap.2 ⟨x, hx, by rw [hxp]; exact hcn.2.2.2.2.2.2.2.1⟩
  · rcases (Bool.eq_false_or_eq_true rr.nv.isLeaf').symm with hb | hb
    · obtain ⟨-, hnd, -⟩ := hnr.2.2.2.2.2.2.2.2.2.2.2.2.1 hb
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
            have := nm_inj_mg W hwm bl B hc _ _ _ hx hyb
            exact hn.1 (List.mem_map.2 ⟨y, hy, this.symm⟩)
      exact key _ hnd
    · have : kidsOf B rr.ws = [] := by
        unfold kidsOf; rw [List.filterMap_eq_nil_iff]; exact hleaf0 hb
      rw [this]; exact List.nodup_nil

include hc in
/-- The new record of an old node other than the parent, the siblings. -/
theorem mg_other (sI sC sI' sC' : GoSlice) (y : Loc) (ry : NRec) (hy : B.ns !! y = some ry)
    (hyp : y ≠ pl) (hyl : y ≠ ll) (hyr : y ≠ lr) :
    (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns !! y =
      some (if ry.nv.parent' = lr then { ry with nv := { ry.nv with parent' := ll } } else ry) := by
  rw [mg_ns, if_neg hyp, if_neg hyl, if_neg hyr, hy]; rfl

/-- Where a node of the bucket after the merge points to: an old node's new record. -/
theorem mg_look (sI sC sI' sC' : GoSlice) (y : Loc) (ry : NRec) (hy : B.ns !! y = some ry)
    (hyr : y ≠ lr) :
    ∃ ry', (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns !! y = some ry' ∧
      ry'.nv.pgid' = ry.nv.pgid' ∧ ry'.nv.isLeaf' = ry.nv.isLeaf' ∧
      ry'.nv.parent' = (if ry.nv.parent' = lr then ll else ry.nv.parent') := by
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, -, -, -, -, -, -, -, hself, -, hnself⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  by_cases hyp : y = pl
  · subst y; rw [hrp] at hy; cases hy
    refine ⟨mgParent rp (k + 1) lr sI' sC', by rw [mg_ns, if_pos rfl], rfl, rfl, ?_⟩
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
    (hp : pagePosAt (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
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
    rw [← getElem?_eraseIdx_mg]; exact hx
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
    bndIn (bnd ll) (wEntryBnd (bnd pl) rp.ws k) ∧ bndIn (bnd lr) (wEntryBnd (bnd pl) rp.ws (k + 1)) := by
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, hpgl, hpgr, -, hnd, -⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  constructor
  · obtain ⟨-, rq, i, x, hrq, hx, hxp, -, hb⟩ := (hk.2.2 ll rl hrl).2.1 (by rw [hp1]; exact hpn)
    rw [hp1, hrp] at hrq; cases hrq
    have : i = k := by
      by_cases h : i = k
      · exact h
      · exact absurd (by rw [hxp, hpgl]) (nodup_pgid_ne_mg rp.ws hnd k i wl x hwl hx h)
    subst this; rw [hp1] at hb; exact hb
  · obtain ⟨-, rq, i, x, hrq, hx, hxp, -, hb⟩ := (hk.2.2 lr rr hrr).2.1 (by rw [hp2]; exact hpn)
    rw [hp2, hrp] at hrq; cases hrq
    have : i = k + 1 := by
      by_cases h : i = k + 1
      · exact h
      · exact absurd (by rw [hxp, hpgr]) (nodup_pgid_ne_mg rp.ws hnd (k + 1) i wr x hwr hx h)
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

end mg

end rbl

end bbolt
end EtcdGrove
end Perennial
