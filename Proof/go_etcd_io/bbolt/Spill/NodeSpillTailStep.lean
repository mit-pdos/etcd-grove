/-
`node.spill` after its children's loop (U9y, `notes/bbolt-proof-plan.md`; pure): **a piece's step
keeps the pieces' loop's invariant** (`pcInv_stepX`, `Spill/NodeSpillTailInv.pcInv_step` over the
corrected step `pcStepX`).

`pcStep` (`Spill/NodeSpillPiecesStep`) misses three facts the invariant needs, which `pcStepX`
adds (U9y's report): the allocation's freelist step (`st` lists only the free's: after an
allocation from the free ids `w2.fl = w1.fl.alloc …`, not `w.fl.applySteps st`), the parent's
inodes' count after its put (`pcPar`'s `ins` is unconstrained), and the piece's new key slice not
nil (`pcRec`'s `r.k0`: `n.key = n.inodes[0].Key()`, a non-empty key).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInv
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailStepState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section step
variable [GooseExts] [GoGlobalContext]

theorem node_ne_null {X : WX} {txid : w64} {ml : Nat} {fl : FLPg} (hG : spG X txid ml fl)
    {bl l : Loc} {r : NRec} (hr : X.node bl l = some r) : l ≠ null := by
  intro he; subst he
  unfold WX.node at hr
  cases e : X.t.bs !! bl with
  | none => rw [e] at hr; cases hr
  | some B =>
    rw [e] at hr
    have := (hG.2.2.1.2.2.1 bl B e).2
    simp only [Option.bind_some] at hr
    rw [this] at hr; cases hr

/-- **A piece's step keeps the invariant** (over `pcStepX`; the free ids no view pages, the
objects disjoint: `spillTail_gen`'s `H3`). -/
theorem pcInv_stepX {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (xs : List (Loc × node × List Inode)) (pl : Loc) (i : Nat) (Xi : WX) (wi : WDb)
    (st : List FLStep) (x : Loc × node × List Inode) (rl : NRec) (X3 : WX) (w2 : WDb)
    (st' : List FLStep) (id : w64)
    (hI : pcInv X w bl n rn O lo hi h D N E cs xs pl i Xi wi st) (hx : xs[i]? = some x)
    (hrl : Xi.node bl x.1 = some rl)
    (hs : pcStepX Xi wi bl x.1 rl (pcCount (insSize rl.ins)) X3 w2 st' id)
    (hd : objsDisj Xi.t) (hfv : ∀ y ∈ wi.fl.free, Xi.v.pages !! y.toNat = none)
    (hlr : insLens rl.ins rl.ws) :
    pcInv X w bl n rn O lo hi h D N E cs xs pl (i + 1) X3 w2 (st ++ st') := by
  obtain ⟨rl', hrl', -, -, hpp⟩ := pcInv_pre hpre hsp xs pl i Xi wi st x hI hx
  rw [hrl] at hrl'; cases hrl'
  replace hpp := hpp hlr
  obtain ⟨X', w', r', st0, T, X2, wss, rp0, bs, j, Es, Ds, ps, stl, hend, hlens, hsr, hfit, rfl,
    hEs, hents, hD, hcs, hL⟩ := hI
  have hil : i < xs.length := (List.getElem?_eq_some_iff.1 hx).1
  obtain ⟨ws, hws⟩ : ∃ ws, wss[i]? = some ws :=
    ⟨_, List.getElem?_eq_getElem (by rw [hsr.len]; exact hil)⟩
  obtain ⟨Sb, Eb, hDi, hEi, hSb⟩ := hents i ws hws
  let pn : Piece := ⟨x.1, id, wssKey wss i, nodePages id.toNat ws.length Sb⟩
  refine ⟨X', w', r', st0, T, X2, wss, rp0, bs, j, Es, Ds, ps ++ [pn], stl ++ st', hend, hlens,
    hsr, hfit, by rw [List.append_assoc], hEs, hents, hD, hcs, ?_⟩
  obtain ⟨hlv, hbl, -, hG1, hne, -, -, -, -, -, -, hparp⟩ := hpp
  obtain ⟨rk, hrk, -, hsim⟩ := hL.todo i x ws (Nat.le_refl _) hx hws
  rw [hrl] at hrk; cases hrk
  obtain ⟨-, -, hxbl, hxlf, -, hxpg, hxpl, hxch, -⟩ := hsr.prec i x ws hx hws
  have hnv : rl.nv = { x.2.1 with key' := rl.nv.key' } := by
    rw [hsim.1]; unfold splitRec; split <;> rfl
  have hrpl : rl.nv.parent' = pl := by rw [hnv]; exact hxpl
  have hGi := hL.step.2.2.2.1
  have hnn : ∀ {l : Loc} {r : NRec}, Xi.node bl l = some r → l ≠ null :=
    fun hr => node_ne_null hGi hr
  have hpl1 : rl.nv.parent' ≠ null → rl.nv.parent' ≠ x.1 := fun h => (hparp h).elim fun _ hh => hh.2.2.1
  obtain ⟨ra, rp, s, ins, q, hX3l, hsa, hpar3, hlive3, hpg3, htx3, hmk3, hext3, hc0, hbuf3,
    hbnone⟩ := pcStepX_state hs hrl hpl1 hG1
  have hG3 := pcStepX_spG hs hrl hlv hne (fun h => ⟨hpl1 h, (hparp h).elim fun _ hh => hh.2.1⟩) hd hG1
    (fun y hy => hL.slot.2.2.2 y hy) hfv hL.vb
  have hfr3 := pcStepX_frame hs hrl hd hG1
  obtain ⟨hPid, hPne⟩ := spP_bufs_insert hbuf3 hpg3
  have hfresh := pcStepX_fresh hs hL.slot
  sorry

end step

end Spill

end bbolt
end EtcdGrove
end Perennial
