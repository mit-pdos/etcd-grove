/-
`node.spill`'s tail (U9z, `notes/bbolt-proof-plan.md`; pure): **the child case's `spDone`** from
the pieces' loop's state at its end (`tail_done_child`), given what the loop's invariant `pcLoop`
does not yet carry (U9z's report): the slots' bookkeeping (`hDk`, `hDn`, `hPd`: as `spLoop`'s
`Dk`, `Dn`, `Pd`, from the spill's start) and the parent's record but its entries (`hpar`: its
children, struct but the inodes, key, the key slice's nil-ness, the split's).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailDonePieces
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailDoneStep

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

/-- The pieces' entries are `n`'s: within its bounds, keys not empty and within
`bboltEntryMax`. -/
theorem tail_ents {X' : WX} {bl n : Loc} {r' : NRec} {lo hi : Option (List w8)}
    {wss : List (List WEntry)} (hun : uNode X' bl n r' lo hi) (hws : wss.flatten = r'.nilCh.ws) :
    ∀ ws ∈ wss, ∀ e ∈ ws, keyIn lo hi e.key ∧ 0 < e.key.length ∧
      e.key.length + e.value.length ≤ bboltEntryMax := by
  intro ws hws' e he
  have : e ∈ r'.ws := by
    show e ∈ r'.nilCh.ws
    rw [← hws]; exact List.mem_flatten.2 ⟨ws, hws', he⟩
  exact hun.2.2.2.2.2.2.1 e this

/-- **The child case's `spDone`** (see the module doc). -/
theorem tail_done_child {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {pl : Loc} {rp : NRec} {j : Nat} {plo phi : Option (List w8)}
    {X' : WX} {w' : WDb} {r' : NRec} {st0 : List FLStep} {T0 : List Loc}
    {X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {rp0 : NRec}
    {bs : List WEntry} {Es : List (List El)} {Ds : List (List Nat)} {ps : List Piece}
    {Xf : WX} {wf : WDb} {stl : List FLStep}
    (hpre : spPre X w bl n rn O lo hi h F D N E (.child pl rp j plo phi))
    (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st0 T0) (hd : objsDisj X'.t)
    (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp0)
    (hEs : Es.flatten = E) (hbs : bs.map wDat = rp.ws.map wDat)
    (hL : pcLoop X' r' X2 w' bl O lo hi h xs wss pl rp0 bs j Es Ds xs.length ps Xf wf stl)
    (hne : ∀ ws ∈ wss, 0 < ws.length)
    (hDk : ∀ s ∈ D, s ∈ pcSlots (spP Xf) ps ∨ s ∈ pendSlots wf.fl)
    (hDn : ∀ s ∈ pcSlots (spP Xf) ps, s ∈ D ∨ newSlot (st0 ++ stl) X.t.mv.pgid'.toNat s)
    (hPd : ∀ x, spP Xf !! x ≠ spP X !! x → x ∉ D)
    (hpar : ∀ rpf, Xf.node bl pl = some rpf → rpf.cs = rp0.cs ∧
      rpf.nv = { rp0.nv with inodes' := rpf.nv.inodes', key' := rpf.nv.key' } ∧
      rpf.key = rp0.key ∧
      (rpf.nv.key' = slice.nil ↔ rp0.nv.key' = slice.nil)) (hpo : parOK Xf bl) :
    spDone X Xf w wf bl n rn O lo hi h D N E (.child pl rp j plo phi) (st0 ++ stl) := by
  obtain ⟨hn', -, hun', hnv, -, -, hfr0, hT0⟩ := spEnd_rec hpre hsp hend
  have hctx : spCtx X bl n rn lo hi N (.child pl rp j plo phi) := by
    rcases hpre.2.2 with ⟨hs, -⟩ | ⟨-, hctx, -⟩
    · rw [hsp] at hs; cases hs
    · exact hctx
  obtain ⟨hrnp, hpl, hplN, hrp, hunp, -, -, -, -, -, -, -, -⟩ := hctx
  have hnN : n ∈ N := by
    rcases hpre.2.2 with ⟨hs, -⟩ | ⟨hut, -⟩
    · rw [hsp] at hs; cases hs
    · exact uTree_head hut
  have hlen0 : xs.length ≠ 0 := fun e => hsr.ne (List.length_eq_zero_iff.1 e)
  -- the parent through the children's loop and `n.children = nil`
  have hplT : pl ∉ N ++ T0 := by
    intro hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hplN hm
    · rw [node_none_of_objs (hT0 pl hm)] at hrp; cases hrp
  obtain ⟨rpX, hrpX, hsimX, -⟩ := spFrame_node hfr0 hrp hplT
  have hne' : pl ≠ n := fun he => hplN (he ▸ hnN)
  have hrp1 : (X'.nilCh bl n r').node bl pl = some rpX := by
    unfold WX.nilCh; rw [killL_node, WX.setNode_node_ne _ _ hne']; exact hrpX
  have hpar0 : rp0 = { rpX with
      nv := ({ rpX.nv with children' := rp0.nv.children' } : node),
      cs := rpX.cs ++ (xs.drop 1).map (·.1) } := by
    have hrN : r'.nilCh.nv.parent' = pl := by
      show r'.nv.parent' = pl; rw [hnv]; exact hrnp
    rcases hsr.par with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, rp1, h1, h2, -⟩
    · rw [hrN] at h1; exact absurd h1 hpl
    · rw [hrN] at h1; exact absurd h1 hpl
    · rw [hrp1] at h1; cases h1; exact h2
  obtain ⟨rpf, hrpf, hplv, -, hcap, -, hws, hins⟩ := hL.par hpl
  obtain ⟨hcs, hnvf, hkey, hknil⟩ := hpar rpf hrpf
  refine ⟨tail_step hpre hend hsr hL.step, Or.inr ⟨hsp,
    T0 ++ r'.cs.filter (fun c => decide (c ∉ N)) ++ (xs.drop 1).map (·.1) ++ [pl],
    pcSlots (spP Xf) ps, tail_frame hpre hsp hend hsr hL.frame hd, ?_, ?_, hDk, hDn, hPd, hpo, ?_⟩⟩
  · intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · rcases tail_T hpre hsp hend hsr l hl with h1 | h1
      · exact Or.inl h1
      · exact absurd h1.1 (fun h => by cases h)
    · exact Or.inr (Or.inl ⟨pl, rp, j, plo, phi, rfl, List.mem_singleton.1 hl⟩)
  · have hs := hL.slot
    have hD0 : Ds.drop xs.length = [] := List.drop_eq_nil_of_le (Nat.le_of_eq hL.Dlen)
    simp only [pcOwn, hlen0, ↓reduceIte, hD0, List.flatten_nil, List.nil_append] at hs
    exact hs
  · refine ⟨ps, rpf, ?_, pcLoop_head hL hsr.head, ?_, rfl, ?_, hrpf, ?_, hplv⟩
    · exact pcLoop_piecesOK hL hsr.len hsr.ne hsr.nd (tail_ents hun' hsr.ws) hne hpl
    · intro x hx
      have hm : x.l ∈ (ps.drop 1).map Piece.l := List.mem_map.2 ⟨x, hx, rfl⟩
      rw [pcLoop_drop hL] at hm
      obtain ⟨y, hy, he⟩ := List.mem_map.1 hm
      rw [← he]; exact tail_fresh hpre hsp hend (hsr.fresh y hy)
    · rw [pcLoop_els hL hsr.len, hEs]
    · refine ⟨by rw [hws, parWs_full hlen0 hbs], ?_, ?_, ?_, ?_, ?_, hins.1⟩
      · rw [hcs, hpar0, pcLoop_drop hL]; simp only [hsimX.2.2.2.2.1]
      · rw [hnvf, hpar0, hsimX.1]
      · rw [hknil, hpar0]; exact hsimX.2.1
      · rw [hkey, hpar0]; exact hsimX.2.2.2.2.2.1
      · rw [hcap]; exact hunp.2.2.2.1.symm

end lemmas

end Spill

end bbolt
end EtcdGrove
end Perennial
