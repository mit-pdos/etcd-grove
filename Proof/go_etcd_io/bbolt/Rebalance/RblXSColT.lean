/-
The logical tree after the root's collapse (U8b, `Rebalance/RblXSteps.lean`): bucket `bl`'s
records `colBkt` (the root `n`, at the root position `P`, takes its only child `lc`'s kind and
entries; `lc`, at `C`, gone) change the logical tree only at `P` and `C`, so `rt_collapse` gives
the tree after (`col_tree`); the other positions keep their extents (`col_posExtent`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSRmT
public import Proof.go_etcd_io.bbolt.Rebalance.RblCol

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section colt
variable [GooseExts]

section
variable (X : WX) (bl : Loc) (B : BRec) (n : Loc) (rn : NRec) (w0 : WEntry) (lc : Loc)
  (rc : NRec) (sI : GoSlice)
  (hb : X.t.bs !! bl = some B) (hc : bktClean X.v X.t.mv.pgid'.toNat bl B) (ha : rblAcyc B)
  (hrn : B.ns !! n = some rn) (hbr : rn.nv.isLeaf' = false) (hpn : rn.nv.parent' = null)
  (hws : rn.ws = [w0]) (hlc : B.nm !! w0.pgid = some lc) (hrc : B.ns !! lc = some rc)
include hb hc ha hrn hbr hpn hws hlc hrc

theorem col_resolve (q : w64) (hq : q ≠ rc.nv.pgid') :
    resolve (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI)) q = resolve B q := by
  obtain ⟨-, -, -, -, -, h0, -⟩ := col_basic X.v _ bl B n rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc
  have h0' : (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI)).ib.root' ≠ W64 0 := h0
  unfold resolve
  rw [if_neg h0', if_neg h0]
  show (GMap.delete rc.nv.pgid' B.nm) !! q = _
  rw [GMap.lookup_delete_ne _ (Ne.symm hq)]

/-- **The other positions keep their extents.** -/
theorem col_posExtent (q : w64) (hq : q ≠ rc.nv.pgid') :
    (X.setBkt bl (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI))).posExtent bl q =
      X.posExtent bl q := by
  obtain ⟨hp1, hlcn, hpe, hnm1, -, h0, -⟩ :=
    col_basic X.v _ bl B n rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc
  unfold WX.posExtent
  rw [setBkt_look, if_pos rfl, hb]
  simp only
  rw [col_resolve X bl B n rn w0 lc rc sI hb hc ha hrn hbr hpn hws hlc hrc q hq]
  cases hres : resolve B q with
  | none => rfl
  | some l =>
    simp only
    have hl : B.nm !! q = some l := by simp only [resolve, if_neg h0] at hres; exact hres
    have hll : l ≠ lc := by
      intro he; subst he; rw [← hpe] at hlc
      exact hq (nm_inj X.v _ bl B hc q _ l hl hlc)
    cases hy : B.ns !! l with
    | none =>
      have := (hc.2.2.2.2.1 q l hl).2
      obtain ⟨r0, hr0, -⟩ := this; rw [hy] at hr0; cases hr0
    | some ry =>
      obtain ⟨ry', hry', hpg', -⟩ :=
        col_look X.v _ bl B n rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc sI l ry hy hll
      rw [hry']
      simp only [Option.map_some, Option.getD_some, hpg']
      rfl

/-- **The tree after the collapse** (`rt_collapse`): finite, its leaves' entries kept, its
positions those before but the child's page `C`. -/
theorem col_tree (hroot : ∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null)
    (hrt : rtOK X bl) :
    rtOK (X.setBkt bl (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI))) bl ∧
    ((X.setBkt bl (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI))).leaves bl).flatten =
      (X.leaves bl).flatten ∧
    (∀ q ∈ (X.setBkt bl (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI))).positions bl,
      q ∈ X.positions bl ∧ q ≠ rc.nv.pgid') ∧
    (∀ q ∈ X.positions bl, q ≠ rc.nv.pgid' →
      q ∈ (X.setBkt bl (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI))).positions bl) := by
  obtain ⟨hp1, hlcn, hpe, hnm1, hpgne, h0, honly, -⟩ :=
    col_basic X.v _ bl B n rn w0 lc rc hc ha hrn hbr hpn hws hlc hrc
  have hnmC : B.nm !! rc.nv.pgid' = some lc := by rw [hpe]; exact hlc
  obtain ⟨t, ht, hp, hh, D, hD⟩ := hrt
  have hnn : n ≠ null := (hc.2.2.2.2.1 _ _ hnm1).1
  have hrootn : B.bv.rootNode' = n := ncol_root (hc.2.2.2.2.2.2.2.1 n rn hrn) hpn
  have htp : t.pid = rn.nv.pgid' := by
    have h1 : t.pid = B.ib.root' := by rw [hp]; simp [WX.rootPid, hb]
    have h2 := hc.2.2.2.1 (by rw [hrootn]; exact hnn)
    rw [hrootn] at h2
    rw [h1]; exact nm_inj X.v _ bl B hc _ _ n h2 hnm1
  let B' := colBkt B n lc rc.nv.pgid' (colRoot rn rc sI)
  let X' := X.setBkt bl B'
  have hb' : X'.t.bs !! bl = some B' := by
    show (X.setBkt bl B').t.bs !! bl = _; rw [setBkt_look, if_pos rfl]
  have hfr := ltree_frame X X' bl B B' (fun q => q = rn.nv.pgid' ∨ q = rc.nv.pgid') hb hb'
    (fun c hc => by show (X.setBkt bl B').t.bs !! c = _; rw [setBkt_look, if_neg hc]) rfl rfl rfl
    rfl rfl
    (fun q hq => by
      show (colBkt B n lc rc.nv.pgid' (colRoot rn rc sI)).nm !! q = _
      rw [col_nm, if_neg (fun h => hq (Or.inr h))])
    (fun q l hq hl => by
      show ((colBkt B n lc rc.nv.pgid' (colRoot rn rc sI)).ns !! l).map NRec.kw = _
      have hln : l ≠ n := fun he => hq (Or.inl (nm_inj X.v _ bl B hc q _ l hl (he ▸ hnm1)))
      have hll : l ≠ lc := fun he => hq (Or.inr (nm_inj X.v _ bl B hc q _ l hl (he ▸ hnmC)))
      rw [col_ns, if_neg hln, if_neg hll]
      cases B.ns !! l with
      | none => rfl
      | some ry =>
        simp only [Option.map_some]
        split <;> rfl)
    (fun h => absurd h h0)
  have hLP : ltree X bl rn.nv.pgid' = some (false, [w0]) := by
    rw [ltree_node_rbl X bl B hb hc h0 n rn hrn, hbr, hws]
  have hLC : ltree X bl rc.nv.pgid' = some (rc.nv.isLeaf', rc.ws) :=
    ltree_node_rbl X bl B hb hc h0 lc rc hrc
  have h'P : ltree X' bl rn.nv.pgid' = some (rc.nv.isLeaf', rc.ws) := by
    show ltree (X.setBkt bl B') bl rn.nv.pgid' = _
    unfold ltree
    rw [setBkt_look, if_pos rfl]
    simp only
    rw [col_resolve X bl B n rn w0 lc rc sI hb hc ha hrn hbr hpn hws hlc hrc _ hpgne,
      resolve_node B X.v _ bl hc h0 n rn hrn]
    simp only
    rw [col_ns, if_pos rfl]
    rfl
  have hedge : ∀ x c, t.edge x c → c = rc.nv.pgid' → x = rn.nv.pgid' := by
    intro x c he hcE
    have := edge_mat X bl B hb hc t ht hp x c he lc rc (by rw [hcE]; exact hnmC) hrc
    rw [hp1] at this
    exact nm_inj X.v _ bl B hc x _ n this hnm1
  obtain ⟨t', ht', hk⟩ := rt_collapse (ltree X) (ltree X') bl t ht rn.nv.pgid' rc.nv.pgid' w0
    rc.nv.isLeaf' rc.ws hpgne htp hLP hpe.symm hLC h'P
    (fun q h1 h2 => hfr bl q (fun _ h => h.elim h1 h2)) hedge
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hk
  have hfuel : X'.fuel = X.fuel := setBkt_fuel X bl B B' hb
  have hrp' : X'.rootPid = X.rootPid := setBkt_rootPid X bl B B' hb rfl
  have hp' : t'.pid = X'.rootPid bl := by rw [hrp', k1, hp]
  have hh' : t'.ht < X'.fuel := by rw [hfuel]; omega
  refine ⟨⟨t', ht', hp', hh', D - 1, k4 D hD⟩, ?_, ?_, ?_⟩
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

end colt

end bbolt
end EtcdGrove
end Perennial
