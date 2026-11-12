/-
The merge of two siblings (`RblMg1.lean`, `RblMg2.lean`): the merged bucket stays clean
(`mg_clean`). Ported from `old/bbolt/.../RebalanceMg.lean`.
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

theorem mg_clean (sI sC sI' sC' : GoSlice) (hkind : rl.nv.isLeaf' = rr.nv.isLeaf')
    (hlt : ∀ x ∈ rl.ws, ∀ y ∈ rr.ws, go.GoStringLt x.key y.key)
    (hleaf0 : rr.nv.isLeaf' = true → ∀ w ∈ rr.ws, B.nm !! w.pgid = none)
    (hroot : B.bv.rootNode' ≠ lr) :
    bktClean W hwm bl (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
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
  have hnm' := mg_nm B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
    (mgLeft rl rr (kidsOf B rr.ws) sI sC)
  have hns' := mg_ns B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
    (mgLeft rl rr (kidsOf B rr.ws) sI sC)
  have hinj := nm_inj_mg W hwm bl B hc
  have hcl := hc
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := hcl
  have hrn : B.bv.rootNode' ≠ null := by
    intro h0; have := (c3 h0).1; rw [this] at hrp; cases hrp
  have hnp := c8 pl rp hrp
  have hnl := c8 ll rl hrl
  have hnr := c8 lr rr hrr
  have hil : k + 1 < rp.ws.length := (List.getElem?_eq_some_iff.1 hwr).1
  have hilen : rp.ins.length = rp.ws.length := hnp.2.2.1
  have hnmr : B.nm !! rr.nv.pgid' = some lr := by rw [hpgr]; exact hlr
  have hnml : B.nm !! rl.nv.pgid' = some ll := by rw [hpgl]; exact hll
  have hpgr' : rr.nv.pgid' ≠ rl.nv.pgid' := by rw [hpgr, hpgl]; exact Ne.symm hpgne
  -- the node of a page other than the right node's
  have hnmo : ∀ c, c ≠ rr.nv.pgid' → (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
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
    exact mem_eraseIdx_of_ne_mg rp.ws (k + 1) x hx (by rw [hwr]; intro h; cases h; exact hne hpgr.symm)
  have hcs' : ∀ c, c ∈ rp.cs.eraseIdx (rp.cs.idxOf lr) ↔ c ≠ lr ∧ c ∈ rp.cs := by
    intro c; rw [cs_erase_mg]; exact List.Nodup.mem_erase_iff hnp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- a child of `q` in the old bucket is one in the new (as `q'`)
  have hchild : ∀ (q : Loc) (l' : Loc) (x : w64), B.nm !! x = some l' → x ≠ rr.nv.pgid' →
      (∀ r', B.ns !! l' = some r' → r'.nv.parent' = q) →
      ∃ r', (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
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
    show (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
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
      obtain ⟨n1, n0, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := hnp
      refine ⟨n1, n0, ?_, wsSorted_eraseIdx_mg _ _ n3, fun x hx => n4 x (List.mem_of_mem_eraseIdx hx),
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
        show ∃ rq', (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
          (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ns !! rp.nv.parent' = some rq' ∧ rq'.nv.isLeaf' = false ∧
          pl ∈ rq'.cs ∧ ∃ w, w ∈ rq'.ws ∧ w.pgid = rp.nv.pgid'
        rw [hother _ rq hrq hnself hql hqr]
        refine ⟨_, rfl, ?_, ?_, x, ?_, hxp⟩ <;> split <;> assumption
      · show (rp.cs.eraseIdx (rp.cs.idxOf lr)).Nodup
        rw [cs_erase_mg]; exact n15.erase _
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
      obtain ⟨n1, n0, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := hnl
      obtain ⟨m1, m0, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16⟩ := hnr
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
          obtain ⟨pgx, hpgx⟩ : ∃ pg, W.pages !! x.pgid.toNat = some pg := by
            cases hwf with
            | page _ pg _ _ hpg _ _ _ => exact ⟨pg, hpg⟩
          have hself' := treeHas.root _ pgx hpgx
          exact c9 ll jx x.pgid lr jy x.pgid hp1' hp2' (by intro h; simp only [Prod.mk.injEq] at h; exact hllr h.1)
            _ hself' hself'
      refine ⟨n1, n0, ?_, ?_, ?_, ?_, n6, ?_, n8, n9, n10, ?_, ?_, fun h => absurd h (by show ¬ rl.nv.parent' = null; rw [hp1]; exact hpn),
        fun _ => ?_, ?_, ?_⟩
      · show (rl.ins ++ rr.ins).length = (rl.ws ++ rr.ws).length
        rw [List.length_append, List.length_append, n2, m2]
      · show wsSorted (rl.ws ++ rr.ws)
        rw [wsSorted_iff_mg] at n3 m3 ⊢
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
      · show ∃ rq : NRec, (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
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
    obtain ⟨n1, n0, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := c8 y ry hry
    have hpgy : ry.nv.pgid' ≠ rr.nv.pgid' := hpos' y hyr _ n7
    have hgen : ∀ ry' : NRec, ry'.ws = ry.ws → ry'.capOwn = ry.capOwn → ry'.cs = ry.cs → ry'.ins = ry.ins → ry'.key = ry.key →
        ry'.ksrc = ry.ksrc → ry'.nv.bucket' = ry.nv.bucket' → ry'.nv.isLeaf' = ry.nv.isLeaf' →
        ry'.nv.spilled' = ry.nv.spilled' → ry'.nv.key' = ry.nv.key' → ry'.nv.pgid' = ry.nv.pgid' →
        ry'.nv.parent' = (if ry.nv.parent' = lr then ll else ry.nv.parent') →
        nodeClean W hwm bl (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
          (mgLeft rl rr (kidsOf B rr.ws) sI sC)) y ry' := by
      intro ry' e1 e0 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
      refine ⟨by rw [e6]; exact n1, by rw [e0]; exact n0, by rw [e3, e1]; exact n2, by rw [e1]; exact n3,
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
            refine ⟨mgParent rp (k + 1) lr sI' sC', by rw [hqp, hns', if_pos rfl], hbq, (hcs' y).2 ⟨hyr, hiq⟩, x,
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
    · exact hgen _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by rw [if_pos ‹_›])
    · exact hgen _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by rw [if_neg ‹_›])
  · intro l1 i1 q1 l2 i2 q2 h1 h2' hne d hd
    obtain ⟨n1, p1'⟩ := mg_pos W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr sI sC sI' sC' hkind l1 i1 q1 h1
    obtain ⟨n2, p2'⟩ := mg_pos W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr sI sC sI' sC' hkind l2 i2 q2 h2'
    refine c9 _ _ q1 _ _ q2 p1' p2' ?_ d hd
    intro he; apply hne
    exact mgPos_inj pl ll lr k rl.ws.length hllp hlrp hllr l1 l2 i1 i2 n1 n2
      (Prod.ext (Prod.mk.inj he).1 (Prod.mk.inj he).2)
  · refine ⟨fun l j q hp d hd => ?_, c11⟩
    obtain ⟨-, p'⟩ := mg_pos W hwm bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr sI sC sI' sC' hkind l j q hp
    rw [hnm']; split
    · rfl
    · exact c10 _ _ q p' d hd

end mg

end rbl

end bbolt
end EtcdGrove
end Perennial
