/-
The logical tree after two siblings' merge (U8c, `Rebalance/RblXMg.lean`): bucket `bl`'s records
`mgBkt` (the right sibling `lr` at page `R` merged into the left one `ll` at page `A`, the parent
`pl` at page `P` without its entry `k + 1`) change the logical tree only at `P`, `A`, `R`
(`ltree_frame`), so `rt_merge` gives the tree after: finite, its leaves' entries and positions
those before but `R`'s (`mg_tree`); the other positions keep their extents (`mg_posExtent`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSRmT
public import Proof.go_etcd_io.bbolt.Rebalance.RblMg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section mgt
variable [GooseExts]

section
variable (X : WX) (bl : Loc) (B : BRec) (pl : Loc) (rp : NRec) (k : Nat)
  (wl wr : WEntry) (ll lr : Loc) (rl rr : NRec) (sI sC sI' sC' : GoSlice)
  (hb : X.t.bs !! bl = some B) (hc : bktClean X.v X.t.mv.pgid'.toNat bl B) (ha : rblAcyc B)
  (hpn : pl ≠ null) (hrp : B.ns !! pl = some rp) (hbr : rp.nv.isLeaf' = false)
  (hwl : rp.ws[k]? = some wl) (hwr : rp.ws[k + 1]? = some wr)
  (hll : B.nm !! wl.pgid = some ll) (hlr : B.nm !! wr.pgid = some lr)
  (hrl : B.ns !! ll = some rl) (hrr : B.ns !! lr = some rr)
include hb hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr

theorem mg_resolve (q : w64) (hq : q ≠ rr.nv.pgid') :
    resolve (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)) q = resolve B q := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h0, -⟩ :=
    mg_basic X.v _ bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have h0' : (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC)).ib.root' ≠ W64 0 := h0
  unfold resolve
  rw [if_neg h0', if_neg h0, mg_nm, if_neg hq]

/-- **The other positions keep their extents.** -/
theorem mg_posExtent (q : w64) (hq : q ≠ rr.nv.pgid') :
    (X.setBkt bl (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC))).posExtent bl q = X.posExtent bl q := by
  obtain ⟨-, -, -, -, -, -, hpgr, -, -, h0, -⟩ :=
    mg_basic X.v _ bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  unfold WX.posExtent
  rw [setBkt_look, if_pos rfl, hb]
  simp only
  rw [mg_resolve X bl B pl rp k wl wr ll lr rl rr sI sC sI' sC' hb hc ha hpn hrp hbr hwl hwr hll hlr
    hrl hrr q hq]
  cases hres : resolve B q with
  | none => rfl
  | some l =>
    simp only
    have hl : B.nm !! q = some l := by simp only [resolve, if_neg h0] at hres; exact hres
    have hlr' : l ≠ lr := by
      intro he; subst he; rw [hpgr] at hq
      exact hq (nm_inj X.v _ bl B hc q _ l hl hlr)
    cases hy : B.ns !! l with
    | none =>
      obtain ⟨-, r0, hr0, -⟩ := hc.2.2.2.2.1 q l hl; rw [hy] at hr0; cases hr0
    | some ry =>
      obtain ⟨ry', hry', hpg', -⟩ :=
        mg_look X.v _ bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
          sI sC sI' sC' l ry hy hlr'
      rw [hry']
      simp only [Option.map_some, Option.getD_some, hpg']
      rfl

/-- **The tree after the merge** (`rt_merge`): finite, its leaves' entries kept, its positions
those before but the right sibling's page `R`. -/
theorem mg_tree (hroot : ∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null)
    (hkind : rl.nv.isLeaf' = rr.nv.isLeaf') (hrt : rtOK X bl) :
    rtOK (X.setBkt bl (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC))) bl ∧
    ((X.setBkt bl (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC))).leaves bl).flatten = (X.leaves bl).flatten ∧
    (∀ q ∈ (X.setBkt bl (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
      (mgLeft rl rr (kidsOf B rr.ws) sI sC))).positions bl, q ∈ X.positions bl ∧ q ≠ rr.nv.pgid') ∧
    (∀ q ∈ X.positions bl, q ≠ rr.nv.pgid' →
      q ∈ (X.setBkt bl (mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
        (mgLeft rl rr (kidsOf B rr.ws) sI sC))).positions bl) := by
  obtain ⟨hp1, hp2, hllr, hllp, hlrp, hpgl, hpgr, hnmP, hnd, h0, -, -, -, hpgne, -⟩ :=
    mg_basic X.v _ bl B pl rp k wl wr ll lr rl rr hc ha hpn hrp hbr hwl hwr hll hlr hrl hrr
  have hnmA : B.nm !! rl.nv.pgid' = some ll := by rw [hpgl]; exact hll
  have hnmR : B.nm !! rr.nv.pgid' = some lr := by rw [hpgr]; exact hlr
  have hPA : rp.nv.pgid' ≠ rl.nv.pgid' := fun he => hllp (by rw [he] at hnmP; rw [hnmA] at hnmP; cases hnmP; rfl)
  have hPR : rp.nv.pgid' ≠ rr.nv.pgid' := fun he => hlrp (by rw [he] at hnmP; rw [hnmR] at hnmP; cases hnmP; rfl)
  have hAR : rl.nv.pgid' ≠ rr.nv.pgid' := by rw [hpgl, hpgr]; exact hpgne
  obtain ⟨t, ht, hp, hh, D, hD⟩ := hrt
  have hrootX : ∀ x l r, t.pid = x → B.nm !! x = some l → B.ns !! l = some r → r.nv.parent' = null := by
    intro x l r he hx hr
    have htp : t.pid = B.ib.root' := by rw [hp]; simp [WX.rootPid, hb]
    have hnn : B.bv.rootNode' ≠ null := by
      intro hn0; have := (hc.2.2.1 hn0).1; rw [this] at hr; simp at hr
    have := hc.2.2.2.1 hnn
    rw [← htp, he, hx] at this
    cases this
    exact hroot r hr
  let B' := mgBkt B pl ll lr rr.nv.pgid' (mgParent rp (k + 1) lr sI' sC')
    (mgLeft rl rr (kidsOf B rr.ws) sI sC)
  let X' := X.setBkt bl B'
  have hb' : X'.t.bs !! bl = some B' := by
    show (X.setBkt bl B').t.bs !! bl = _; rw [setBkt_look, if_pos rfl]
  have hfr := ltree_frame X X' bl B B'
    (fun q => q = rp.nv.pgid' ∨ q = rl.nv.pgid' ∨ q = rr.nv.pgid') hb hb'
    (fun c hc => by show (X.setBkt bl B').t.bs !! c = _; rw [setBkt_look, if_neg hc]) rfl rfl rfl
    rfl rfl
    (fun q hq => by
      show (mgBkt B pl ll lr rr.nv.pgid' _ _).nm !! q = _
      rw [mg_nm, if_neg (fun h => hq (Or.inr (Or.inr h)))])
    (fun q l hq hl => by
      show ((mgBkt B pl ll lr rr.nv.pgid' _ _).ns !! l).map NRec.kw = _
      have hlp : l ≠ pl := fun he => hq (Or.inl (nm_inj X.v _ bl B hc q _ l hl (he ▸ hnmP)))
      have hll' : l ≠ ll := fun he => hq (Or.inr (Or.inl (nm_inj X.v _ bl B hc q _ l hl (he ▸ hnmA))))
      have hlr' : l ≠ lr := fun he => hq (Or.inr (Or.inr (nm_inj X.v _ bl B hc q _ l hl (he ▸ hnmR))))
      rw [mg_ns, if_neg hlp, if_neg hll', if_neg hlr']
      cases B.ns !! l with
      | none => rfl
      | some ry =>
        simp only [Option.map_some]
        split <;> rfl)
    (fun h => absurd h h0)
  have hLP : ltree X bl rp.nv.pgid' = some (false, rp.ws) := by
    rw [ltree_node_rbl X bl B hb hc h0 pl rp hrp, hbr]
  have hLA : ltree X bl rl.nv.pgid' = some (rl.nv.isLeaf', rl.ws) :=
    ltree_node_rbl X bl B hb hc h0 ll rl hrl
  have hLR : ltree X bl rr.nv.pgid' = some (rl.nv.isLeaf', rr.ws) := by
    rw [ltree_node_rbl X bl B hb hc h0 lr rr hrr, hkind]
  have h'P : ltree X' bl rp.nv.pgid' = some (false, rp.ws.eraseIdx (k + 1)) := by
    show ltree (X.setBkt bl B') bl rp.nv.pgid' = _
    unfold ltree
    rw [setBkt_look, if_pos rfl]
    simp only
    rw [mg_resolve X bl B pl rp k wl wr ll lr rl rr sI sC sI' sC' hb hc ha hpn hrp hbr hwl hwr hll hlr
      hrl hrr _ hPR, resolve_node B X.v _ bl hc h0 pl rp hrp]
    simp only
    rw [mg_ns, if_pos rfl]
    simp only [Option.map_some, mgParent, hbr]
  have h'A : ltree X' bl rl.nv.pgid' = some (rl.nv.isLeaf', rl.ws ++ rr.ws) := by
    show ltree (X.setBkt bl B') bl rl.nv.pgid' = _
    unfold ltree
    rw [setBkt_look, if_pos rfl]
    simp only
    rw [mg_resolve X bl B pl rp k wl wr ll lr rl rr sI sC sI' sC' hb hc ha hpn hrp hbr hwl hwr hll hlr
      hrl hrr _ hAR, resolve_node B X.v _ bl hc h0 ll rl hrl]
    simp only
    rw [mg_ns, if_neg hllp, if_pos rfl]
    simp only [Option.map_some, mgLeft]
  have hedge : ∀ x c, t.edge x c → (c = rl.nv.pgid' ∨ c = rr.nv.pgid') → x = rp.nv.pgid' := by
    intro x c he hcE
    rcases hcE with hcE | hcE
    · have := edge_mat X bl B hb hc t ht hp x c he ll rl (by rw [hcE]; exact hnmA) hrl
      rw [hp1] at this
      exact nm_inj X.v _ bl B hc x _ pl this hnmP
    · have := edge_mat X bl B hb hc t ht hp x c he lr rr (by rw [hcE]; exact hnmR) hrr
      rw [hp2] at this
      exact nm_inj X.v _ bl B hc x _ pl this hnmP
  have hrootAR : t.pid ≠ rl.nv.pgid' ∧ t.pid ≠ rr.nv.pgid' := by
    refine ⟨fun he => ?_, fun he => ?_⟩
    · have := hrootX _ ll rl he hnmA hrl; rw [hp1] at this; exact hpn this
    · have := hrootX _ lr rr he hnmR hrr; rw [hp2] at this; exact hpn this
  obtain ⟨t', ht', hk⟩ := rt_merge (ltree X) (ltree X') bl t ht rp.nv.pgid' rl.nv.pgid' rr.nv.pgid'
    k rp.ws rl.ws rr.ws rl.nv.isLeaf' wl wr hPA hPR hAR hLP hwl hwr hnd hpgl.symm hpgr.symm hLA hLR
    h'P h'A (fun q h1 h2 h3 => hfr bl q (fun _ h => h.elim h1 (fun h => h.elim h2 h3)))
    hrootAR hedge
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

end mgt

end bbolt
end EtcdGrove
end Perennial
