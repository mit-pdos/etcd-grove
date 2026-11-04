/-
`node.spill`'s tail (U9z, `notes/bbolt-proof-plan.md`; pure): **the pieces at the loop's end**,
from `pcLoop` at `i = xs.length`: `piecesOK` (`pcLoop_piecesOK`), their leaf elements in order
(`pcLoop_els`), the first piece `n` (`pcLoop_head`), the pieces' nodes the split's
(`pcLoop_ls`), and the parent's entries (`parWs_full`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInv
public import Proof.go_etcd_io.bbolt.Spill.UTreeFrame
public import Proof.go_etcd_io.bbolt.Spill.STreeWrite

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section lemmas
variable [GooseExts] [GoGlobalContext]

/-- At the loop's end, piece `k` exists for each split piece `k`. -/
theorem pcLoop_get {X' : WX} {r' : NRec} {X2 : WX} {w2 : WDb} {bl : Loc} {O : List Nat}
    {hi : Option (List w8)} {h : Nat} {xs : List (Loc × node × List Inode)}
    {wss : List (List WEntry)} {pl : Loc} {bs : List WEntry} {j : Nat} {Es : List (List El)}
    {Ds : List (List Nat)} {ps : List Piece} {Xf : WX} {wf : WDb} {stl : List FLStep}
    (hL : pcLoop X' r' X2 w2 bl O hi h xs wss pl bs j Es Ds xs.length ps Xf wf stl)
    (hlen : wss.length = xs.length) {k : Nat} {p : Piece} (hp : ps[k]? = some p) :
    ∃ x ws, xs[k]? = some x ∧ wss[k]? = some ws ∧ p.l = x.1 := by
  have hk : k < xs.length := by rw [← hL.len]; exact (List.getElem?_eq_some_iff.1 hp).1
  have hx : xs[k]? = some xs[k] := List.getElem?_eq_getElem hk
  exact ⟨_, _, hx, List.getElem?_eq_getElem (by rw [hlen]; exact hk), hL.pcl k p _ hp hx⟩

/-- The pieces' nodes are the split's. -/
theorem pcLoop_ls {X' : WX} {r' : NRec} {X2 : WX} {w2 : WDb} {bl : Loc} {O : List Nat}
    {hi : Option (List w8)} {h : Nat} {xs : List (Loc × node × List Inode)}
    {wss : List (List WEntry)} {pl : Loc} {bs : List WEntry} {j : Nat} {Es : List (List El)}
    {Ds : List (List Nat)} {ps : List Piece} {Xf : WX} {wf : WDb} {stl : List FLStep}
    (hL : pcLoop X' r' X2 w2 bl O hi h xs wss pl bs j Es Ds xs.length ps Xf wf stl) :
    ps.map Piece.l = xs.map (·.1) := by
  apply List.ext_getElem (by simp [hL.len])
  intro k h1 h2
  simp only [List.getElem_map]
  have hk : k < ps.length := by simpa using h1
  have hk' : k < xs.length := by simpa using h2
  exact hL.pcl k _ _ (List.getElem?_eq_getElem hk) (List.getElem?_eq_getElem hk')

/-- The first piece is `n`. -/
theorem pcLoop_head {X' : WX} {r' : NRec} {X2 : WX} {w2 : WDb} {bl : Loc} {O : List Nat}
    {hi : Option (List w8)} {h : Nat} {xs : List (Loc × node × List Inode)}
    {wss : List (List WEntry)} {pl : Loc} {bs : List WEntry} {j : Nat} {Es : List (List El)}
    {Ds : List (List Nat)} {ps : List Piece} {Xf : WX} {wf : WDb} {stl : List FLStep} {n : Loc}
    (hL : pcLoop X' r' X2 w2 bl O hi h xs wss pl bs j Es Ds xs.length ps Xf wf stl)
    (hhd : (xs.head?.map (·.1)) = some n) : (ps.head?.map Piece.l) = some n := by
  rw [← List.head?_map, pcLoop_ls hL, List.head?_map, hhd]

/-- The pieces after the first are the split's fresh nodes. -/
theorem pcLoop_drop {X' : WX} {r' : NRec} {X2 : WX} {w2 : WDb} {bl : Loc} {O : List Nat}
    {hi : Option (List w8)} {h : Nat} {xs : List (Loc × node × List Inode)}
    {wss : List (List WEntry)} {pl : Loc} {bs : List WEntry} {j : Nat} {Es : List (List El)}
    {Ds : List (List Nat)} {ps : List Piece} {Xf : WX} {wf : WDb} {stl : List FLStep}
    (hL : pcLoop X' r' X2 w2 bl O hi h xs wss pl bs j Es Ds xs.length ps Xf wf stl) :
    (ps.drop 1).map Piece.l = (xs.drop 1).map (·.1) := by
  rw [List.map_drop, pcLoop_ls hL, List.map_drop]

/-- The pieces' leaf elements are `Es`'s, in order. -/
theorem pcLoop_els {X' : WX} {r' : NRec} {X2 : WX} {w2 : WDb} {bl : Loc} {O : List Nat}
    {hi : Option (List w8)} {h : Nat} {xs : List (Loc × node × List Inode)}
    {wss : List (List WEntry)} {pl : Loc} {bs : List WEntry} {j : Nat} {Es : List (List El)}
    {Ds : List (List Nat)} {ps : List Piece} {Xf : WX} {wf : WDb} {stl : List FLStep}
    (hL : pcLoop X' r' X2 w2 bl O hi h xs wss pl bs j Es Ds xs.length ps Xf wf stl)
    (hlen : wss.length = xs.length) :
    ps.flatMap (fun x => treeEls (spP Xf) x.id.toNat) = Es.flatten := by
  have hE : ps.map (fun x => treeEls (spP Xf) x.id.toNat) = Es := by
    apply List.ext_getElem (by simp [hL.len, hL.Elen])
    intro k h1 h2
    simp only [List.getElem_map]
    have hk : k < ps.length := by simpa using h1
    obtain ⟨x, ws, hx, hw, -⟩ := pcLoop_get hL hlen (List.getElem?_eq_getElem hk)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hf⟩ :=
      hL.done k x _ ws hx (List.getElem?_eq_getElem hk) hw
    rw [hf.2.2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  rw [List.flatMap_def, hE]

/-- **The pieces at the loop's end are `piecesOK`** (under a parent): from `done`, the pieces'
entries (`n`'s, within `[lo, hi)`, keys not empty and within `bboltEntryMax`) and the pieces not
empty. -/
theorem pcLoop_piecesOK {X' : WX} {r' : NRec} {X2 : WX} {w2 : WDb} {bl : Loc} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {xs : List (Loc × node × List Inode)}
    {wss : List (List WEntry)} {pl : Loc} {bs : List WEntry} {j : Nat} {Es : List (List El)}
    {Ds : List (List Nat)} {ps : List Piece} {Xf : WX} {wf : WDb} {stl : List FLStep}
    (hL : pcLoop X' r' X2 w2 bl O hi h xs wss pl bs j Es Ds xs.length ps Xf wf stl)
    (hlen : wss.length = xs.length) (hxs : xs ≠ []) (hnd : (xs.map (·.1)).Nodup)
    (hent : ∀ ws ∈ wss, ∀ e ∈ ws, keyIn lo hi e.key ∧ 0 < e.key.length ∧
      e.key.length + e.value.length ≤ bboltEntryMax)
    (hne : ∀ ws ∈ wss, 0 < ws.length) (hpl : pl ≠ null) :
    piecesOK Xf bl pl (spP Xf) Xf.t.mv.pgid'.toNat lo hi h ps := by
  refine ⟨?_, by rw [pcLoop_ls hL]; exact hnd, ?_⟩
  · intro e; have := hL.len; rw [e] at this
    exact hxs (List.length_eq_zero_iff.1 this.symm)
  intro k p hp
  obtain ⟨x, ws, hx, hw, hpx⟩ := pcLoop_get hL hlen hp
  obtain ⟨rk, hrk, hlv, hbl, hspl, hcs, -, hpar, hpg, hdat, hk, hkey, hf⟩ :=
    hL.done k x p ws hx hp hw
  have hwsm : ws ∈ wss := List.mem_of_getElem? hw
  have h0 : 0 < ws.length := hne ws hwsm
  have hk0 : p.k = ws[0].key := by
    rw [hk]; unfold wssKey wKey; rw [hw]; simp [List.getElem?_eq_getElem h0]
  obtain ⟨hkin, hkl, hkb⟩ := hent ws hwsm _ (List.getElem_mem h0)
  have hpk : ∀ m, m < ps.length → pcKey ps m = wssKey wss m := by
    intro m hm
    have hpm : ps[m]? = some ps[m] := List.getElem?_eq_getElem hm
    obtain ⟨xm, wm, hxm, hwm, -⟩ := pcLoop_get hL hlen hpm
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hkm, -⟩ := hL.done m xm _ wm hxm hpm hwm
    unfold pcKey; rw [hpm]; exact hkm
  rw [← hpx] at hrk hlv
  refine ⟨rk, hrk, hlv, hbl, hspl, hcs, hpar, hpg, (hkey hpl).1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [length_of_dat hdat]; exact h0
  · rw [hk0]; exact hkin
  · rw [hk0]; exact hkl
  · rw [hk0]; omega
  · have hb : childHi hi (pcKey ps) ps.length k = childHi hi (wssKey wss) xs.length k := by
      rw [hL.len]; exact childHi_congr (fun hm => hpk _ (by rw [hL.len]; exact hm))
    rw [hb]
    obtain ⟨hs, hpg', he⟩ := hf
    exact ⟨hs, hpg', rfl⟩

/-- **The parent's entries at the loop's end** (`parentSpilled`'s first clause): the base's with
entry `j` replaced by the pieces'. -/
theorem parWs_full {bs : List WEntry} {rp : NRec} {j i : Nat} {ps : List Piece} (hi : i ≠ 0)
    (hbs : bs.map wDat = rp.ws.map wDat) :
    parWs bs j i ps = (rp.ws.take j).map wDat ++ ps.map pcDat ++ (rp.ws.drop (j + 1)).map wDat := by
  unfold parWs
  simp only [hi, ↓reduceIte]
  rw [List.map_take, List.map_drop, hbs, ← List.map_take, ← List.map_drop]

end lemmas

end Spill

end bbolt
end EtcdGrove
end Perennial
