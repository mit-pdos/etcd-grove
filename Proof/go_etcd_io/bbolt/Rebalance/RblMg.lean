/-
Two siblings merged by `node.rebalance` (`ll`, `lr`: the children of the parent `pl` at its
entries `k`, `k + 1`): the right one's materialized children reparented to the left one, which
gets the right one's entries; the parent's entry for the right one removed (`del`,
`removeChild`), the right one dropped (`delete(b.nodes, ...)`, its page freed). The bucket
`mgBkt` stays clean (`mg_clean`, `RblMg3.lean`), keeps its keys (`mg_keys`, `RblMg4.lean`: the
merged node's bounds the join of the two; the right one's first child's bound is the right one's
first key, `brFirst`), its parent pointers without cycle (`mg_acyc`), its heights (`mg_ht`: both
siblings one below the parent, so their children are of one kind), and the nested buckets'
entries (`mg_entryIn`); `rbl_mg` puts them together (pure; the old tokens part, `nodeToks_merge`,
`mg_toks`, is gone with the tokens). Ported from `old/bbolt/.../RebalanceMg.lean`; the
definitions are in `RblMg1.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblMg3
public import Proof.go_etcd_io.bbolt.Rebalance.RblMg4

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

theorem mg_acyc (sI sC sI' sC' : GoSlice) :
    rblAcyc (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
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
    rblHt W (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)) := by
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, hpgl, hpgr, -⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have honly := mg_only W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  obtain ⟨ht, pht, hp, hh⟩ := hht
  have hhl : ht ll + 1 = ht pl := ((hh pl rp hrp).2 hbr wl (List.mem_of_getElem? hwl)).1 ll hll
  have hhr : ht lr + 1 = ht pl := ((hh pl rp hrp).2 hbr wr (List.mem_of_getElem? hwr)).1 lr hlr
  have hnm' := mg_nm B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
    (mgLeft rl rr (kidsOf B rr.ws) sI sC)
  have hent : ∀ y ry, B.ns !! y = some ry → ry.nv.isLeaf' = false → ∀ x ∈ ry.ws, x.pgid ≠ rr.nv.pgid' →
      (∀ l', (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)).nm !! x.pgid = some l' → ht l' + 1 = ht y) ∧
      ((mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)).nm !! x.pgid = none → pht (x.pgid.toNat) + 1 = ht y) := by
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
    (hy : (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
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
    entryIn W (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)) kk v := by
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, hpgl, hpgr, -⟩ :=
    mg_basic W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have hns' := mg_ns B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
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
    have hn' : (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)).nm !! W64 (c : Int) = none := by
      rw [mg_nm, if_neg (by rw [← hxc]; exact hxn)]; exact hn
    by_cases hyp : y = pl
    · subst y
      rw [hrp] at hy; cases hy
      have hji : j0 ≠ k + 1 := by intro he; subst he; rw [hwr] at hx; cases hx; exact hxn hpgr.symm
      refine ⟨pl, if j0 < k + 1 then j0 else j0 - 1, ⟨mgParent rp (k + 1) lr sI' sC', x,
        by rw [hns', if_pos rfl], hyb, ?_, hxc, hn'⟩, hlt⟩
      show (rp.ws.eraseIdx (k + 1))[if j0 < k + 1 then j0 else j0 - 1]? = some x
      rw [getElem?_eraseIdx_mg]
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

/-- Two siblings merged (`ll`, `lr`: the parent `pl`'s entries `k`, `k + 1`, one of them the
deficient node): the bucket in the invariant, the parent the deficient node. -/
theorem rbl_mg (W : View) (hwm : Nat) (bl : Loc) (B : BRec) (pl : Loc) (rp : NRec) (k : Nat)
    (wl wr : WEntry) (ll lr : Loc) (rl rr : NRec) (nl : Loc) (sI sC sI' sC' : GoSlice)
    (HB : rblB W hwm bl B (some nl)) (hnl : nl = ll ∨ nl = lr) (hp0 : W.pages !! 0 = none)
    (hpn : pl ≠ null) (hrp : B.ns !! pl = some rp) (hbr : rp.nv.isLeaf' = false)
    (hwl : rp.ws[k]? = some wl) (hwr : rp.ws[k + 1]? = some wr)
    (hll : B.nm !! wl.pgid = some ll) (hlr : B.nm !! wr.pgid = some lr)
    (hrl : B.ns !! ll = some rl) (hrr : B.ns !! lr = some rr) (hne : 0 < (rl.ws ++ rr.ws).length) :
    rblB W hwm bl (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)) (some pl) ∧
      (∀ kk v, entryIn W B kk v → entryIn W (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC)) kk v) ∧
      (∀ y ry', (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
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
      have hwf := (hc.2.2.2.2.2.2.2.1 l0 r0 hr0).2.2.2.2.2.2.2.2.2.1 hroot0
      rw [hpg0] at hwf
      cases hwf with
      | page _ pg _ _ hpg _ _ _ => rw [show (W64 0).toNat = 0 from rfl, hp0] at hpg; cases hpg
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

end rbl

end bbolt
end EtcdGrove
end Perennial
