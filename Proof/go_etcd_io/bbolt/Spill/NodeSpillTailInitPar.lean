/-
`node.spill` after its children's loop (U9w2, `notes/bbolt-proof-plan.md`; pure): **the pieces'
parent at the loop's start** (`tail_init_par`, `pcInv_init`'s context clause and `pcLoop.par`):
in the child case the context's parent, its entries `rp.ws` (`bs`) kept modulo sources through
the children's loop and the kill; in the top case split in two or more, the new parent (no
entries); unsplit, none.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInv
public import Proof.go_etcd_io.bbolt.Spill.UTreeFrame
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailDoneStep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section par
variable [GooseExts] [GoGlobalContext]

theorem newParent_parent (nv : node) (cs : GoSlice) : (newParent nv cs).parent' = null := rfl

/-- A piece of the split is not its parent (the piece's parent is `pl`, not null). -/
theorem split_pl_not_piece {X1 X2 : WX} {bl n : Loc} {rN : NRec}
    {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {pl : Loc} {rp' : NRec}
    (hsr : splitRel X1 X2 bl n rN xs wss pl rp') (hpl : pl ≠ null) (hrp : X2.node bl pl = some rp')
    (hnull : rp'.nv.parent' = null) : pl ∉ xs.map (·.1) := by
  intro hm
  obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
  have hil : i < wss.length := by rw [hsr.len]; exact (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨h1, -, -, -, -, -, hpar, -⟩ := hsr.prec i x _ hi (List.getElem?_eq_getElem hil)
  rw [e, hrp] at h1; cases h1
  rw [show (splitRec rN x _ _ _).nv = x.2.1 by unfold splitRec; split <;> rfl] at hnull
  exact hpl (hpar.symm.trans hnull)

/-- **The pieces' parent at the loop's start** (see the module doc). -/
theorem tail_init_par {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    {X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {pl : Loc}
    {rp' : NRec}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T)
    (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp') :
    ∃ (bs : List WEntry) (j : Nat),
      (match cs with
       | .child pl' rp j' _ _ => pl = pl' ∧ j = j' ∧ bs.map wDat = rp.ws.map wDat
       | .top => bs = [] ∧ j = 0) ∧
      (pl ≠ null → ∃ rpi, X2.node bl pl = some rpi ∧ pl ∈ X2.live ∧ pl ∉ xs.map (·.1) ∧
        rpi.capOwn = true ∧ wsSorted rpi.ws ∧ rpi.ws.map wDat = parWs bs j 0 [] ∧
        rpi.ins.length = rpi.ws.length ∧
        rpi.cs = rp'.cs ∧ rpi.nv = { rp'.nv with inodes' := rpi.nv.inodes', key' := rpi.nv.key' } ∧
        rpi.key = rp'.key ∧
        (rpi.nv.key' = slice.nil ↔ rp'.nv.key' = slice.nil)) := by
  obtain ⟨hn', -, -, hnv, -, -, hfr0, hT⟩ := spEnd_rec hpre hsp hend
  obtain ⟨-, -, hS⟩ := tail_pre hpre hsp hend
  have hpar : r'.nilCh.nv.parent' = rn.nv.parent' := by
    show r'.nv.parent' = rn.nv.parent'; rw [hnv]
  have hnN : n ∈ N := by
    rcases hpre.2.2 with ⟨hs, -⟩ | ⟨hut, -⟩
    · rw [hsp] at hs; cases hs
    · exact uTree_head hut
  have hctx : spCtx X bl n rn lo hi N cs := by
    rcases hpre.2.2 with ⟨hs, -⟩ | ⟨-, hctx, -⟩
    · rw [hsp] at hs; cases hs
    · exact hctx
  cases cs with
  | top =>
    refine ⟨[], 0, ⟨rfl, rfl⟩, fun hpl => ?_⟩
    rcases hsr.par with ⟨-, -, e⟩ | ⟨-, -, -, -, hrp0, hrp, hlv⟩ | ⟨h1, -⟩
    · exact absurd e hpl
    · refine ⟨rp', hrp, hlv, split_pl_not_piece hsr hpl hrp (by rw [hrp0]; rfl), ?_, ?_, ?_, ?_,
        rfl, ?_, rfl, Iff.rfl⟩
      · rw [hrp0]; rfl
      · rw [hrp0]; intro i j _ hj; exact absurd hj (Nat.not_lt_zero _)
      · rw [hrp0]; rfl
      · rw [hrp0]; rfl
      · cases rp'; rfl
    · rw [hpar] at h1; exact absurd hctx.1 h1
  | child pl' rp j' plo phi =>
    obtain ⟨hpl', hpln, hplN, hrp, hunp, -⟩ := hctx
    refine ⟨rp.ws, j', ?_, fun hpl => ?_⟩
    all_goals rcases hsr.par with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, hplr, rp1, hrp1, hrp0, hrp2, hlv⟩
    all_goals try (rw [hpar, hpl'] at h1; exact absurd h1 hpln)
    · rw [hplr, hpar, hpl']; exact ⟨rfl, rfl, rfl⟩
    · rw [hpar, hpl'] at hplr; subst hplr
      have hplT : pl ∉ N ++ T := by
        intro hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hplN hm
        · rw [node_none_of_objs (hT pl hm)] at hrp; cases hrp
      obtain ⟨rpX, hrpX, hsim, -⟩ := spFrame_node hfr0 hrp hplT
      have hne : pl ≠ n := fun e => hplN (e ▸ hnN)
      have hrpX' : (X'.nilCh bl n r').node bl pl = some rpX := by
        unfold WX.nilCh; rw [killL_node, WX.setNode_node_ne _ _ hne]; exact hrpX
      have e : rpX = rp1 := by rw [hrpX'] at hrp1; exact Option.some.inj hrp1
      subst e
      have hlvX : pl ∈ (X'.nilCh bl n r').live := by
        obtain ⟨rq, hrq, hlq⟩ := hS.2.2.2.2.2.2.2 (by rw [hpar, hpl']; exact hpln)
        rw [hpar, hpl'] at hrq hlq; exact hlq
      have hnotx : pl ∉ xs.map (·.1) := by
        rw [xs_map_head hsr.head]
        simp only [List.mem_cons, List.mem_map]
        rintro (e | ⟨x, hx, e⟩)
        · exact hne e
        · rw [← e, node_none_of_objs (hsr.fresh x hx)] at hrpX'; cases hrpX'
      obtain ⟨-, -, hws, hins, -, -, hcap⟩ := hsim
      have hlen : rpX.ws.length = rp.ws.length := length_of_dat hws
      refine ⟨rp', hrp2, hlv.2 hlvX, hnotx, ?_, ?_, ?_, ?_, rfl, ?_, rfl, Iff.rfl⟩
      · rw [hrp0]; show rpX.capOwn = true; rw [hcap]; exact hunp.2.2.2.1
      · rw [hrp0]; exact wsSorted_of_dat hws hunp.2.2.2.2.2.1
      · rw [hrp0]; exact hws
      · rw [hrp0]; show rpX.ins.length = rpX.ws.length; rw [hins, hlen]; exact hunp.2.2.2.2.1
      · cases rp'; rfl

end par

end Spill

end bbolt
end EtcdGrove
end Perennial
