/-
`node.spill`'s tail (U9w4, `notes/bbolt-proof-plan.md`; pure): **the pieces' loop's end without a
new root** (`pcInv_doneX`, what `Spill/NodeSpillPieces.spillTail_wp` passes `spillTail_gen` as
`H6`): from the invariant `pcInv` at the end, the child case by `tail_done_child`, the unsplit top
node by `tail_done_top1`. Both take the bucket's parent pointers at the end (`tail_parOK`: from the
children's loop's, through `n.children = nil`, the split and the pieces' loop: `parOK_nilCh`,
`parOK_split`, `parOK_pcLoop`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailDoneChild
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailDoneTop
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitMain
public import Proof.go_etcd_io.bbolt.Spill.ParOK

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

/-- No bucket has a node at `null`. -/
theorem node_null_of_deref {X : WX} (h : derefPre X) (bl : Loc) : X.node bl null = none := by
  unfold WX.node
  cases hB : X.t.bs !! bl with
  | none => rfl
  | some B => exact derefPre_null h bl B hB

/-- The children's loop's parent pointers. -/
theorem spEnd_parOK {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) : parOK X' bl := by
  rcases hend with ⟨-, hX, -⟩ | ⟨-, h', es, i, -, hl, -⟩
  · rcases hpre.2.2 with ⟨hs, -⟩ | ⟨-, -, -, -, -, -, -, hpo⟩
    · rw [hsp] at hs; cases hs
    · rw [hX]; exact hpo
  · exact hl.par

/-- **The bucket's parent pointers in the pieces' loop** (at any iteration). -/
theorem tail_parOK {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st0 : List FLStep} {T0 : List Loc}
    {X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {pl : Loc}
    {rp0 : NRec} {bs : List WEntry} {j : Nat} {Es : List (List El)} {Ds : List (List Nat)}
    {i : Nat} {ps : List Piece} {Xi : WX} {wi : WDb} {stl : List FLStep}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st0 T0) (hd : objsDisj X'.t)
    (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp0)
    (hL : pcLoop X' r' X2 w' bl O lo hi h xs wss pl rp0 bs j Es Ds i ps Xi wi stl) :
    parOK Xi bl := by
  have hpar' := spEnd_parOK hpre hsp hend
  obtain ⟨hn', -⟩ := spEnd_rec hpre hsp hend
  obtain ⟨-, -, hS1, -, -, -, -, -, -, hS7⟩ := tail_pre hpre hsp hend
  have hG' := (spEnd_step hpre hend).2.2.2.1
  have hG2 := spG_tailSplit hpre hsp hend hd hsr
  have hnn : n ≠ null := by
    intro e; rw [e, node_null_of_deref hG'.2.2.1] at hn'; cases hn'
  have hnull1 : (X'.nilCh bl n r').node bl null = none := by
    unfold WX.nilCh; rw [killL_node, WX.setNode_node_ne _ _ (Ne.symm hnn)]
    exact node_null_of_deref hG'.2.2.1 bl
  have hnull2 := node_null_of_deref hG2.2.2.1 bl
  have hnulli := node_null_of_deref hL.step.2.2.2.1.2.2.1 bl
  have h1 : parOK (X'.nilCh bl n r') bl := parOK_nilCh hpar' hn'
  have hcs0 : r'.nilCh.cs = [] := by simp [NRec.nilCh]
  have h2 : parOK X2 bl := parOK_split h1 hsr.tosplitRel0 hS1 hcs0 hnull1 hnull2
  have hpc := split_pieces hsr.tosplitRel0 hcs0
  obtain ⟨x0, hx0⟩ : ∃ x0, xs[0]? = some x0 := by
    cases e : xs with
    | nil => exact absurd e hsr.ne
    | cons a _ => exact ⟨a, rfl⟩
  obtain ⟨w0, hw0⟩ : ∃ w0, wss[0]? = some w0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hsr.len]; exact (List.getElem?_eq_some_iff.1 hx0).1)⟩
  obtain ⟨B, hB, -⟩ := node_bs_of (hsr.prec 0 x0 w0 hx0 hw0).1
  refine parOK_pcLoop h2 hL hB hsr.len (fun x hx => by obtain ⟨-, -, -, -, a⟩ := hpc x hx; exact a)
    (fun x hx => by obtain ⟨rx, a, -, b, -⟩ := hpc x hx; exact ⟨rx, a, b⟩) ?_ hnull2 hnulli
  intro hpn
  rcases hsr.par with ⟨-, -, e⟩ | ⟨-, -, -, -, -, a, b⟩ | ⟨-, e, rp, -, -, a, b⟩
  · exact absurd e hpn
  · exact ⟨a, b⟩
  · refine ⟨a, b.2 ?_⟩
    rw [e] at hpn ⊢
    obtain ⟨-, -, a⟩ := hS7 hpn
    exact a

/-- **The pieces' entries are not empty** in the child case (split: `splitRel.plen`; unsplit: `n`'s
entries, a child's not empty, `spCtx`, or a branch's at least two). -/
theorem tail_wss_pos {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {pl : Loc} {rp : NRec} {j : Nat} {plo phi : Option (List w8)}
    {X' : WX} {w' : WDb} {r' : NRec} {st0 : List FLStep} {T0 : List Loc}
    {X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {pl' : Loc}
    {rp0 : NRec}
    (hpre : spPre X w bl n rn O lo hi h F D N E (.child pl rp j plo phi))
    (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st0 T0)
    (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl' rp0) :
    ∀ ws ∈ wss, 0 < ws.length := by
  intro ws hws
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hws
  have hkl : k < xs.length := by rw [← hsr.len]; exact (List.getElem?_eq_some_iff.1 hk).1
  by_cases h2 : 2 ≤ xs.length
  · exact (hsr.plen k _ ws (List.getElem?_eq_getElem hkl) hk).2 h2
  have hw1 : wss.length = 1 := by
    rw [hsr.len]; have := List.length_pos_iff.2 hsr.ne; omega
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hw1
  have hwa : ws = a := by rw [ha] at hws; simpa using hws
  have hwr : ws = r'.ws := by
    have e := hsr.ws
    rw [ha] at e
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at e
    rw [hwa, e]; rfl
  rw [hwr]
  rcases hend with ⟨-, -, -, hr, -, -⟩ | ⟨-, h', es, i', -, hl, -⟩
  · rcases hpre.2.2 with ⟨hs, -⟩ | ⟨-, hctx, -⟩
    · rw [hsp] at hs; cases hs
    · rw [hr]; exact hctx.2.2.2.2.2.2.2.2.2.2.2.2.2
  · have := hl.br.two; omega

/-- **The post without a new root** (`spillTail_gen`'s `H6`; see the module doc). -/
theorem pcInv_doneX {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (xs : List (Loc × node × List Inode)) (pl : Loc) (Xf : WX) (wf : WDb) (st : List FLStep)
    (hI : pcInv X w bl n rn O lo hi h D N E cs xs pl xs.length Xf wf st)
    (hc : pl = null ∨ ∃ rp, Xf.node bl pl = some rp ∧ rp.nv.pgid' ≠ W64 0) :
    spDone X Xf w wf bl n rn O lo hi h D N E cs st := by
  obtain ⟨X', w', r', st0, T, X2, wss, rp0, bs, j, Es, Ds, ps, stl, hend, -, hd, hsr, -, rfl, hEs,
    -, ⟨hDk, hDn, hPd⟩, hcs, hL⟩ := hI
  have hpo := tail_parOK hpre hsp hend hd hsr hL
  have hlen0 : xs.length ≠ 0 := fun e => hsr.ne (List.length_eq_zero_iff.1 e)
  have hD0 : Ds.drop xs.length = [] := List.drop_eq_nil_of_le (Nat.le_of_eq hL.Dlen)
  have hown : pcOwn X' r' Ds xs.length ps Xf = pcSlots (spP Xf) ps := by
    simp only [pcOwn, hlen0, ↓reduceIte, hD0, List.flatten_nil, List.nil_append]
  rw [hown] at hDk hDn
  cases cs with
  | child pl' rp j' plo phi =>
    obtain ⟨rfl, rfl, hbs⟩ := hcs
    have hpl : pl ≠ null := by
      rcases hpre.2.2 with ⟨hs, -⟩ | ⟨-, hctx, -⟩
      · rw [hsp] at hs; cases hs
      · exact hctx.2.1
    refine tail_done_child hpre hsp hend hd hsr hEs hbs hL (tail_wss_pos hpre hsp hend hsr) hDk
      hDn hPd (fun rpf hrpf => ?_) hpo
    obtain ⟨rpi, hrpi, -, -, -, -, -, -, hcs', hnv, hkey, hknil⟩ := hL.par hpl
    rw [hrpi] at hrpf; cases hrpf
    exact ⟨hcs', hnv, hkey, hknil⟩
  | top =>
    obtain ⟨rfl, rfl⟩ := hcs
    have hrN : r'.nilCh.nv.parent' = null := by
      obtain ⟨-, -, -, hnv, -⟩ := spEnd_rec hpre hsp hend
      show r'.nv.parent' = null; rw [hnv]
      rcases hpre.2.2 with ⟨hs, -⟩ | ⟨-, hctx, -⟩
      · rw [hsp] at hs; cases hs
      · exact hctx.1
    have hpl : pl = null := by
      rcases hc with h0 | ⟨rpx, hrpx, hpg⟩
      · exact h0
      refine Classical.byContradiction fun hpn => ?_
      obtain ⟨rpi, hrpi, -, -, -, -, -, -, -, hnv, -⟩ := hL.par hpn
      rw [hrpi] at hrpx; cases hrpx
      apply hpg
      have h0 : rp0.nv.pgid' = W64 0 := by
        rcases hsr.par with ⟨-, -, h1⟩ | ⟨-, -, -, -, hrp0, -⟩ | ⟨h1, -⟩
        · exact absurd h1 hpn
        · rw [hrp0]; rfl
        · exact absurd hrN h1
      rw [hnv]; exact h0
    subst hpl
    refine tail_done_top1 hpre hsp hend hd hsr hEs hL hDk hDn hPd (fun p hp => ?_) hpo
    have hl0 : 0 < xs.length := Nat.pos_of_ne_zero hlen0
    obtain ⟨rk, -, -, -, -, -, -, -, -, -, -, -, hf⟩ := hL.done 0 _ p _
      (List.getElem?_eq_getElem hl0) hp (List.getElem?_eq_getElem (by rw [hsr.len]; exact hl0))
    exact (hf.2 rfl).1

end lemmas

end Spill

end bbolt
end EtcdGrove
end Perennial
