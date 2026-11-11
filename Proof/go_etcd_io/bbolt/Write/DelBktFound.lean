/-
U7p (`notes/bbolt-proof-plan.md`): **the deleted name is in the leaf** `c.node()` returns
(`dbk_found`, for `Write/DelBktWp`): the stack routing `n` ends at a leaf of the logical tree whose
entries hold `n` (`LR.route_main`, sorted: `LR.bInvL_leaf`); the materializations keep that leaf's
data (`matGrow_ldat`, as `LR.matGrow_route`), and the node at the last position is that leaf.
-/
module

public import Proof.go_etcd_io.bbolt.Read.LeafFor
public import Proof.go_etcd_io.bbolt.Read.PubWGet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section found
variable [GooseExts]

/-- `wsFound` reads the entries' keys only. -/
theorem wsFound_keys (k : List w8) : ∀ (ws1 ws2 : List WEntry),
    ws1.map WEntry.key = ws2.map WEntry.key → wsFound ws1 k → wsFound ws2 k := by
  have hidx : ∀ (ws1 ws2 : List WEntry), ws1.map WEntry.key = ws2.map WEntry.key →
      wsIdx ws1 k = wsIdx ws2 k := by
    intro ws1
    induction ws1 with
    | nil => intro ws2 h; cases ws2 with
      | nil => rfl
      | cons _ _ => simp at h
    | cons a t ih =>
      intro ws2 h
      cases ws2 with
      | nil => simp at h
      | cons b u =>
        simp only [List.map_cons, List.cons.injEq] at h
        unfold wsIdx at ih ⊢
        simp only [List.takeWhile_cons, h.1]
        split <;> simp [ih u h.2]
  have hget : ∀ (ws1 ws2 : List WEntry), ws1.map WEntry.key = ws2.map WEntry.key → ∀ i : Nat,
      (ws1[i]?).map WEntry.key = (ws2[i]?).map WEntry.key := by
    intro ws1 ws2 h i
    rw [← List.getElem?_map, ← List.getElem?_map, h]
  intro ws1 ws2 h hf
  unfold wsFound at hf ⊢
  rw [← hidx ws1 ws2 h, ← hget ws1 ws2 h]; exact hf

/-- **Materializations keep the data of a route's positions.** -/
theorem matGrow_ldat (k : List w8) (pids : List w64) :
    ∀ X X' bl, matGrow X X' bl → wOK X → LR.lRoute (ltree X) bl k pids →
      pids.head? = some (X.rootPid bl) →
      ∀ p ∈ pids, ldat (ltree X' bl p) = ldat (ltree X bl p) := by
  intro X X' bl h
  induction h with
  | refl X bl => intro _ _ _ _ _; rfl
  | step X Y Z bl l pgid parent hadd hpos _ ih =>
    intro hok hr hh p hp
    have hY := Write.wOK_nodeAdded X Y bl l pgid parent hok hadd hpos
    have hf := wOK_matFresh X Y bl l pgid parent hok hadd hpos
    have hadd' := hadd
    obtain ⟨B, pa, pg, r, ns', bv', hB, hpg, hnm, hl0, hlo, hrb, hrp, hrid, hrleaf, hru, hrs,
      hrcs, hrco, hrws, hrlive, hrkey, hrks, hrins, hrkn, hrvs, hcase, hX'⟩ := hadd'
    have hrp0 : Y.rootPid bl = X.rootPid bl := by
      rw [hX']; unfold WX.rootPid; simp only [GMap.lookup_insert, hB]; rfl
    have hdat : ∀ p ∈ pids, ldat (ltree Y bl p) = ldat (ltree X bl p) := fun p hp =>
      ltree_nodeAdded' X Y bl l pgid parent hadd hf bl p
        (fun _ B' hB' hin => LR.wOK_route_inline X bl B' hok hB' hin k pids hr hh p hp)
    rw [ih hY (LR.lRoute_ldat _ _ bl k pids hr hdat) (by rw [hrp0]; exact hh) p hp, hdat p hp]

/-- **The deleted name is in the leaf** `c.node()` returns. -/
theorem dbk_found (X5 X6 : WX) (l : Loc) (B6 : BRec) (rl : NRec) (n : GoString)
    (els : List elemRef) (pids : List w64) (hok5 : wOK X5) (hp : lPath X5 X5.rl els pids)
    (hr : lRoutes X5 X5.rl els pids n) (hmg : matGrow X5 X6 X5.rl)
    (hB6 : X6.t.bs !! X5.rl = some B6) (hrl : B6.ns !! l = some rl)
    (hres : ∃ pid, pids.getLast? = some pid ∧ resolve B6 pid = some l)
    (hin : ∃ w ∈ lLeaf X5 X5.rl pids, w.key = n) :
    wsFound rl.ws n := by
  obtain ⟨-, B, hB, hc, ⟨bnd, hbk⟩, -, -, hv⟩ := PubW.bktLocalOK_of_wOK X5 hok5 X5.rl _
    (Option.isSome_iff_exists.1 hok5.1.2.2.2.2.1).choose_spec
  have hR := LR.lRoute_of X5 X5.rl els pids n hp hr
  obtain ⟨last, b', ws, hgl, hL, -, hI, -⟩ :=
    LR.route_main X5 X5.rl B bnd _ hB hc hbk hv n pids hR hp.2.2.1
  have hleaf : lLeaf X5 X5.rl pids = ws := by unfold lLeaf; rw [hgl]; simp only [hL]
  have hs := (LR.bInvL_leaf X5 X5.rl B bnd _ hB hc hbk hv last b' hI ws hL).1
  obtain ⟨w, hw, hwk⟩ := hin
  rw [hleaf] at hw
  have hf5 : wsFound ws n := hwk ▸ LR.wsFound_of_mem ws hs w hw
  obtain ⟨pid, hgl', hres'⟩ := hres
  rw [hgl] at hgl'; cases hgl'
  have hd := matGrow_ldat n pids X5 X6 X5.rl hmg hok5 hR hp.2.2.1 last
    (List.mem_of_getLast? hgl)
  have hL6 : ltree X6 X5.rl last = some (rl.nv.isLeaf', rl.ws) := by
    unfold ltree; rw [hB6]; simp only [hres', hrl, Option.map_some]
  rw [hL6, hL] at hd
  simp only [ldat, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
  have hk : ws.map WEntry.key = rl.ws.map WEntry.key := by
    have e := congrArg (List.map fun x : w32 × w64 × List w8 × List w8 => x.2.2.1) hd.2
    simp only [List.map_map] at e
    exact e.symm
  exact wsFound_keys n ws rl.ws hk hf5

end found

end Write

end bbolt
end EtcdGrove
end Perennial
