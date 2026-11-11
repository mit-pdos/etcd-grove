/-
The logical tree after an empty leaf's removal (U8b, `Rebalance/RblXSteps.lean`): bucket `bl`'s
records `rmBkt` (the leaf `n` at page `E` gone from its parent `pl` at page `P`) change the
logical tree only at `P` (one entry less) and `E` (`ltree_frame`), so `rt_remove` gives the tree
after: finite, its leaves' entries and positions those before but `E`'s (`rm_tree`); the other
positions keep their extents (`rm_posExtent`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSPos
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSSim
public import Proof.go_etcd_io.bbolt.Rebalance.RblRm

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rmt
variable [GooseExts]

theorem lposF_congr (L L' : LTree) (bl : Loc) (h : ∀ q, L bl q = L' bl q) :
    ∀ n p, lposF L bl n p = lposF L' bl n p := by
  intro n
  induction n with
  | zero => intro p; rfl
  | succ n ih => intro p; simp only [lposF, h p, ih]

theorem lleaves_congr (L L' : LTree) (bl : Loc) (h : ∀ q, L bl q = L' bl q) :
    ∀ n p, lleaves L bl n p = lleaves L' bl n p := by
  intro n
  induction n with
  | zero => intro p; rfl
  | succ n ih => intro p; simp only [lleaves, h p, ih]

/-- What a bucket-record change keeps of the logical tree's walks: the other buckets' trees, the
fuel and the root positions. -/
theorem setBkt_ltree_other (X : WX) (bl : Loc) (B' : BRec) (c : Loc) (hc : c ≠ bl) :
    ltree (X.setBkt bl B') c = ltree X c := by
  funext q; unfold ltree; rw [setBkt_look, if_neg hc]; rfl

theorem setBkt_fuel (X : WX) (bl : Loc) (B B' : BRec) (hb : X.t.bs !! bl = some B) :
    (X.setBkt bl B').fuel = X.fuel := by
  apply fuel_eq X (X.setBkt bl B') rfl
  intro c; rw [setBkt_look]; split
  · subst c; rw [hb]; rfl
  · rfl

theorem setBkt_rootPid (X : WX) (bl : Loc) (B B' : BRec) (hb : X.t.bs !! bl = some B)
    (hib : B'.ib = B.ib) : (X.setBkt bl B').rootPid = X.rootPid := by
  funext c; unfold WX.rootPid; rw [setBkt_look]; split
  · subst c; rw [hb]; simp only [Option.map_some, Option.getD_some, hib]
  · rfl

theorem setBkt_positions_other (X : WX) (bl : Loc) (B B' : BRec) (hb : X.t.bs !! bl = some B)
    (hib : B'.ib = B.ib) (c : Loc) (hc : c ≠ bl) :
    (X.setBkt bl B').positions c = X.positions c := by
  unfold WX.positions
  rw [setBkt_fuel X bl B B' hb, setBkt_rootPid X bl B B' hb hib]
  exact lposF_congr _ _ c (fun q => by rw [setBkt_ltree_other X bl B' c hc]) _ _

theorem setBkt_posExtent_other (X : WX) (bl : Loc) (B' : BRec) (c : Loc) (hc : c ≠ bl) :
    (X.setBkt bl B').posExtent c = X.posExtent c := by
  funext q; unfold WX.posExtent; rw [setBkt_look, if_neg hc]; rfl

theorem setBkt_rtOK_other (X : WX) (bl : Loc) (B B' : BRec) (hb : X.t.bs !! bl = some B)
    (hib : B'.ib = B.ib) (c : Loc) (hc : c ≠ bl) (h : rtOK X c) :
    rtOK (X.setBkt bl B') c := by
  obtain ⟨t, ht, hp, hh, hD⟩ := h
  refine ⟨t, ?_, by rw [setBkt_rootPid X bl B B' hb hib]; exact hp,
    by rw [setBkt_fuel X bl B B' hb]; exact hh, hD⟩
  have : ltIs (ltree (X.setBkt bl B')) c t ↔ ltIs (ltree X) c t := by
    constructor
    · intro h; exact rt_frame _ _ c t h (fun q _ => by rw [setBkt_ltree_other X bl B' c hc])
    · intro h; exact rt_frame _ _ c t h (fun q _ => by rw [setBkt_ltree_other X bl B' c hc])
  exact this.2 ht

theorem setBkt_leaves_other (X : WX) (bl : Loc) (B B' : BRec) (hb : X.t.bs !! bl = some B)
    (hib : B'.ib = B.ib) (c : Loc) (hc : c ≠ bl) :
    (X.setBkt bl B').leaves c = X.leaves c := by
  unfold WX.leaves
  rw [setBkt_fuel X bl B B' hb, setBkt_rootPid X bl B B' hb hib]
  exact lleaves_congr _ _ c (fun q => by rw [setBkt_ltree_other X bl B' c hc]) _ _

section
variable (X : WX) (bl : Loc) (B : BRec) (n : Loc) (r : NRec) (pl : Loc) (rp : NRec) (i : Nat)
  (w : WEntry) (sI sC : GoSlice)
  (hb : X.t.bs !! bl = some B) (hc : bktClean X.v X.t.mv.pgid'.toNat bl B)
  (hroot : ∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null)
  (hr : B.ns !! n = some r) (hleaf : r.nv.isLeaf' = true) (hemp : r.ws = [])
  (hpl : r.nv.parent' = pl) (hpn : pl ≠ null) (hrp : B.ns !! pl = some rp)
  (hw : rp.ws[i]? = some w) (hwp : w.pgid = r.nv.pgid')
include hb hc hr hleaf hpl hpn hrp hw hwp

theorem rm_resolve (q : w64) (hq : q ≠ r.nv.pgid') :
    resolve (rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC)) q = resolve B q := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h0⟩ :=
    rm_basic X.v _ bl B n r pl rp i w hc hr hleaf hpl hpn hrp hw hwp
  have h0' : (rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC)).ib.root' ≠ W64 0 := h0
  unfold resolve
  rw [if_neg h0', if_neg h0]
  show (GMap.delete r.nv.pgid' B.nm) !! q = _
  rw [GMap.lookup_delete_ne _ (Ne.symm hq)]

/-- **The other positions keep their extents.** -/
theorem rm_posExtent (q : w64) (hq : q ≠ r.nv.pgid') :
    (X.setBkt bl (rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC))).posExtent bl q =
      X.posExtent bl q := by
  obtain ⟨-, -, -, hnm1, hnm2, -, -, -, -, h0⟩ :=
    rm_basic X.v _ bl B n r pl rp i w hc hr hleaf hpl hpn hrp hw hwp
  unfold WX.posExtent
  rw [setBkt_look, if_pos rfl, hb]
  simp only
  rw [rm_resolve X bl B n r pl rp i w sI sC hb hc hr hleaf hpl hpn hrp hw hwp q hq]
  cases hres : resolve B q with
  | none => rfl
  | some l =>
    simp only
    have hl : B.nm !! q = some l := by simp only [resolve, if_neg h0] at hres; exact hres
    have hln : l ≠ n := by
      intro he; subst he; exact hq (nm_inj X.v _ bl B hc q _ l hl hnm1)
    rw [rm_ns]
    by_cases hlp : l = pl
    · subst hlp; rw [if_pos rfl, hrp]; rfl
    · rw [if_neg hlp, if_neg hln]; rfl

include hemp hroot in
/-- **The tree after the removal** (`rt_remove`): finite, its leaves' entries kept, its positions
those before but the leaf's page `E`. -/
theorem rm_tree (hrt : rtOK X bl) :
    rtOK (X.setBkt bl (rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC))) bl ∧
    ((X.setBkt bl (rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC))).leaves bl).flatten =
      (X.leaves bl).flatten ∧
    (∀ q ∈ (X.setBkt bl (rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC))).positions bl,
      q ∈ X.positions bl ∧ q ≠ r.nv.pgid') ∧
    (∀ q ∈ X.positions bl, q ≠ r.nv.pgid' →
      q ∈ (X.setBkt bl (rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC))).positions bl) := by
  obtain ⟨hbr, hin, hnlpl, hnm1, hnm2, hpg, hnotp, honly, hnd, h0⟩ :=
    rm_basic X.v _ bl B n r pl rp i w hc hr hleaf hpl hpn hrp hw hwp
  have hpgP : rp.nv.pgid' ≠ r.nv.pgid' := hpg
  obtain ⟨t, ht, hp, hh, D, hD⟩ := hrt
  have hrootE : t.pid ≠ r.nv.pgid' := by
    intro he
    have htp : t.pid = B.ib.root' := by rw [hp]; simp [WX.rootPid, hb]
    have hnn : B.bv.rootNode' ≠ null := by
      intro hn0; have := (hc.2.2.1 hn0).1; rw [this] at hr; simp at hr
    have := hc.2.2.2.1 hnn
    rw [← htp, he, hnm1] at this
    cases this
    have := hroot r hr; rw [hpl] at this; exact hpn this
  let B' := rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC)
  let X' := X.setBkt bl B'
  have hb' : X'.t.bs !! bl = some B' := by
    show (X.setBkt bl B').t.bs !! bl = _; rw [setBkt_look, if_pos rfl]
  have hfr := ltree_frame X X' bl B B' (fun q => q = rp.nv.pgid' ∨ q = r.nv.pgid') hb hb'
    (fun c hc => by show (X.setBkt bl B').t.bs !! c = _; rw [setBkt_look, if_neg hc]) rfl rfl rfl
    rfl rfl
    (fun q hq => by
      show (rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC)).nm !! q = _
      rw [rm_nm, if_neg (fun h => hq (Or.inr h))])
    (fun q l hq hl => by
      show ((rmBkt B n pl r.nv.pgid' (rmParent rp i n sI sC)).ns !! l).map NRec.kw = _
      rw [rm_ns]
      have hlp : l ≠ pl := fun he => hq (Or.inl (nm_inj X.v _ bl B hc q _ l hl (he ▸ hnm2)))
      have hln : l ≠ n := fun he => hq (Or.inr (nm_inj X.v _ bl B hc q _ l hl (he ▸ hnm1)))
      rw [if_neg hlp, if_neg hln])
    (fun h => absurd h h0)
  have hLP : ltree X bl rp.nv.pgid' = some (false, rp.ws) := by
    rw [ltree_node_rbl X bl B hb hc h0 pl rp hrp, hbr]
  have hLE : ltree X bl r.nv.pgid' = some (true, []) := by
    rw [ltree_node_rbl X bl B hb hc h0 n r hr, hleaf, hemp]
  have h'P : ltree X' bl rp.nv.pgid' = some (false, rp.ws.eraseIdx i) := by
    show ltree (X.setBkt bl B') bl rp.nv.pgid' = _
    unfold ltree
    rw [setBkt_look, if_pos rfl]
    simp only
    rw [rm_resolve X bl B n r pl rp i w sI sC hb hc hr hleaf hpl hpn hrp hw hwp _ hpgP,
      resolve_node B X.v _ bl hc h0 pl rp hrp]
    simp only
    rw [rm_ns, if_pos rfl]
    simp only [Option.map_some, rmParent, hbr]
  have hedge : ∀ x c, t.edge x c → c = r.nv.pgid' → x = rp.nv.pgid' := by
    intro x c he hcE
    have := edge_mat X bl B hb hc t ht hp x c he n r (by rw [hcE]; exact hnm1) hr
    rw [hpl] at this
    exact nm_inj X.v _ bl B hc x _ pl this hnm2
  obtain ⟨t', ht', hk⟩ := rt_remove (ltree X) (ltree X') bl t ht rp.nv.pgid' r.nv.pgid' i rp.ws w
    hpgP hLP hw hwp hnd hLE h'P (fun q h1 h2 => hfr bl q (fun _ h => h.elim h1 h2)) hrootE hedge
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hk
  have hfuel : X'.fuel = X.fuel := setBkt_fuel X bl B B' hb
  have hrp' : X'.rootPid = X.rootPid := setBkt_rootPid X bl B B' hb rfl
  have hp' : t'.pid = X'.rootPid bl := by rw [hrp', k1, hp]
  have hh' : t'.ht < X'.fuel := by rw [hfuel]; omega
  refine ⟨⟨t', ht', hp', hh', D, fun x hx => by have := k4 D hD x hx; omega⟩, ?_, ?_, ?_⟩
  · rw [leaves_rt X' bl t' ht' hp' hh', leaves_rt X bl t ht hp hh, k2]
  · intro q hq
    rw [positions_rt X' bl t' ht' hp' hh'] at hq
    rw [positions_rt X bl t ht hp hh]
    exact k5 q hq
  · intro q hq hqE
    rw [positions_rt X bl t ht hp hh] at hq
    rw [positions_rt X' bl t' ht' hp' hh']
    exact k6 q hq hqE

end

end rmt

end bbolt
end EtcdGrove
end Perennial
