/-
`node.spill`'s tail (U9w4, `notes/bbolt-proof-plan.md`; pure): **the new root's spill**
(`pcInv_topX`, what `Spill/NodeSpillPieces.spillTail_wp` passes `spillTail_gen` as `H7`): a top
node split in two or more under a new root `pl` (page id `0`; in the child case the parent has a
page, `tail_child_pgid`). Its pre (`Spill/NodeSpillTailTopPre`), and its success giving `n`'s: the
steps and frames composed, the touched nodes those of both spills but `n`'s tree (each fresh at
the start, or one of `n`'s children kept modulo sources), the slots through the pieces', and the
final root reached from `n` through `pl`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailTopPre

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

private theorem node_ns {X : WX} {bl : Loc} {B : BRec} (hB : X.t.bs !! bl = some B) (l : Loc) :
    X.node bl l = B.ns !! l := by
  unfold WX.node; rw [hB]; rfl

/-- **In the child case the parent has a page** at the pieces' loop's end (its record's at the
start modulo its slices). -/
theorem tail_child_pgid {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {pl : Loc} {rpc : NRec} {j : Nat} {plo phi : Option (List w8)}
    {X' : WX} {w' : WDb} {r' : NRec} {st0 : List FLStep} {T0 : List Loc}
    {X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {rp0 : NRec}
    {bs : List WEntry} {j' : Nat} {Es : List (List El)} {Ds : List (List Nat)} {ps : List Piece}
    {Xf : WX} {wf : WDb} {stl : List FLStep} {rp : NRec}
    (hpre : spPre X w bl n rn O lo hi h F D N E (.child pl rpc j plo phi))
    (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st0 T0)
    (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp0)
    (hL : pcLoop X' r' X2 w' bl O lo hi h xs wss pl rp0 bs j' Es Ds xs.length ps Xf wf stl)
    (hrp : Xf.node bl pl = some rp) : rp.nv.pgid' ≠ W64 0 := by
  obtain ⟨hn', -, -, hnv, -, -, hfr0, hT0⟩ := spEnd_rec hpre hsp hend
  have hctx : spCtx X bl n rn lo hi N (.child pl rpc j plo phi) := by
    rcases hpre.2.2 with ⟨hs, -⟩ | ⟨-, hctx, -⟩
    · rw [hsp] at hs; cases hs
    · exact hctx
  have hnN : n ∈ N := by
    rcases hpre.2.2 with ⟨hs, -⟩ | ⟨hut, -⟩
    · rw [hsp] at hs; cases hs
    · exact uTree_head hut
  obtain ⟨hrnp, hpl, hplN, hrpc, -, -, hpg0, -⟩ := hctx
  have hplT : pl ∉ N ++ T0 := by
    intro hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hplN hm
    · rw [node_none_of_objs (hT0 pl hm)] at hrpc; cases hrpc
  obtain ⟨rpX, hrpX, hsimX, -⟩ := spFrame_node hfr0 hrpc hplT
  have hne' : pl ≠ n := fun he => hplN (he ▸ hnN)
  have hrp1 : (X'.nilCh bl n r').node bl pl = some rpX := by
    unfold WX.nilCh; rw [killL_node, WX.setNode_node_ne _ _ hne']; exact hrpX
  have hrN : r'.nilCh.nv.parent' = pl := by
    show r'.nv.parent' = pl; rw [hnv]; exact hrnp
  obtain ⟨rpi, hrpi, -, -, -, -, -, -, -, hnvi, -⟩ := hL.par hpl
  rw [hrp] at hrpi; cases hrpi
  rcases hsr.par with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, rp1, h1, h2, -⟩
  · rw [hrN] at h1; exact absurd h1 hpl
  · rw [hrN] at h1; exact absurd h1 hpl
  · rw [hrp1] at h1; cases h1
    have e : rp.nv.pgid' = rpc.nv.pgid' := by
      rw [hnvi]; show rp0.nv.pgid' = _; rw [h2]; show rpX.nv.pgid' = _; rw [hsimX.1]
    rw [e]; exact hpg0

/-- **The new root's spill** (`spillTail_gen`'s `H7`; see the module doc). -/
theorem pcInv_topX {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (xs : List (Loc × node × List Inode)) (pl : Loc) (Xf : WX) (wf : WDb) (st : List FLStep)
    (rp : NRec) (hI : pcInv X w bl n rn O lo hi h D N E cs xs pl xs.length Xf wf st)
    (hpl : pl ≠ null) (hrp : Xf.node bl pl = some rp) (hpg : rp.nv.pgid' = W64 0)
    (hvc : Xf.v = View.ofC Xf.v.base wf.C) :
    ∃ h2 F2 D2 N2, spPre Xf wf bl pl rp O lo hi h2 F2 D2 N2 E .top ∧
      ∀ Xg wg st2, spDone Xf Xg wf wg bl pl rp O lo hi h2 D2 N2 E .top st2 →
        spDone X Xg w wg bl n rn O lo hi h D N E cs (st ++ st2) := by
  obtain ⟨X', w', r', st0, T0, X2, wss, rp0, bs, j, Es, Ds, ps, stl, hend, -, hd, hsr, -, rfl, hEs,
    -, ⟨hDk, hDn, hPd⟩, hcs, hL⟩ := hI
  have hlen0 : xs.length ≠ 0 := fun e => hsr.ne (List.length_eq_zero_iff.1 e)
  have hD0 : Ds.drop xs.length = [] := List.drop_eq_nil_of_le (Nat.le_of_eq hL.Dlen)
  have hown : pcOwn X' r' Ds xs.length ps Xf = pcSlots (spP Xf) ps := by
    simp only [pcOwn, hlen0, ↓reduceIte, hD0, List.flatten_nil, List.nil_append]
  rw [hown] at hDk hDn
  cases cs with
  | child pl' rpc j' plo phi =>
    obtain ⟨rfl, rfl, -⟩ := hcs
    exact absurd hpg (tail_child_pgid hpre hsp hend hsr hL hrp)
  | top =>
  obtain ⟨rfl, rfl⟩ := hcs
  obtain ⟨h2, hfr1, hplv, hcsP, hpnull, hleaf, hspl, hbl, hcap, hsort, hws, hins⟩ :=
    tail_top_par hpre hsp hend hsr hL hpl hrp
  obtain ⟨-, -, hun', -⟩ := spEnd_rec hpre hsp hend
  have hne : ∀ ws ∈ wss, 0 < ws.length := by
    intro ws hws
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hws
    have hkl : k < xs.length := by rw [← hsr.len]; exact (List.getElem?_eq_some_iff.1 hk).1
    exact (hsr.plen k _ ws (List.getElem?_eq_getElem hkl) hk).2 h2
  have hpk := pcLoop_piecesOK hL hsr.len hsr.ne hsr.nd (tail_ents hun' hsr.ws) hne hpl
  have hut := tail_top_uTree (lo := lo) (hi := hi) (h := h) hrp hpg hpk hplv
    (hcsP.trans (pcLoop_ls hL).symm) hleaf hspl hbl hcap hsort hws hins (by rw [hL.len]; exact h2)
  rw [pcLoop_els hL hsr.len, hEs] at hut
  -- the facts at the start
  have hu0 := hpre.2.2
  rcases hu0 with ⟨hs, -⟩ | ⟨hut0, hctx0, -, -, -, hfc0, htl0, -⟩
  · rw [hsp] at hs; cases hs
  obtain ⟨hrn0, B0, hB0, hroot0, hchain0⟩ := hctx0
  have hnN : n ∈ N := uTree_head hut0
  have hfrA := tail_frame hpre hsp hend hsr hL.frame hd
  have hstA := tail_step hpre hend hsr hL.step
  have hmk : X.t.mv.pgid'.toNat ≤ Xf.t.mv.pgid'.toNat := hfrA.2.2.2.2.2.2.2.2.1
  obtain ⟨Bf, hBf, hsimB, -⟩ := hfrA.2.2.2.2.2.2.2.2.2.2.2.2.2.1 B0 hB0
  -- `n` at the end: a piece under `pl`
  have hl0 : 0 < xs.length := Nat.pos_of_ne_zero hlen0
  obtain ⟨x0, hx0⟩ : ∃ x0, xs[0]? = some x0 := ⟨_, List.getElem?_eq_getElem hl0⟩
  have hx0n : x0.1 = n := by
    have := hsr.head; rw [List.head?_eq_getElem?, hx0] at this; simpa using this
  obtain ⟨p0, hp0⟩ : ∃ p0, ps[0]? = some p0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hL.len]; exact hl0)⟩
  obtain ⟨w0, hw0⟩ : ∃ w0, wss[0]? = some w0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hsr.len]; exact hl0)⟩
  obtain ⟨rk, hrk, -, -, hspk, -, -, hpark, -⟩ := hL.done 0 x0 p0 w0 hx0 hp0 hw0
  rw [hx0n] at hrk
  -- the chain: the old one's nodes kept, then `n`, then `pl`
  have hK : ∀ x, onChain B0 B0.bv.rootNode' n x → x ≠ n → ∃ r0 rf, B0.ns !! x = some r0 ∧
      Bf.ns !! x = some rf ∧ rf.nv.parent' = r0.nv.parent' ∧ rf.nv.spilled' = true := by
    intro x hx hne
    obtain ⟨rx, hrx, hspx⟩ := hchain0 x hx hne
    have hxN : x ∉ N := by
      intro hm
      obtain ⟨r2, hr2, hs2⟩ := uTree_N_unspilled hut0 x hm
      rw [hrx] at hr2; cases hr2; rw [hspx] at hs2; cases hs2
    obtain ⟨rf, hrf, hsim⟩ := tail_kept hpre hsp hend hsr hL.frame (Or.inr hfr1) hxN hrx
    refine ⟨rx, rf, by rw [← node_ns hB0]; exact hrx, by rw [← node_ns hBf]; exact hrf,
      nodeSim_parent hsim, ?_⟩
    rw [hsim.1]; exact hspx
  obtain ⟨hrootf, hchainf⟩ := chain_ext (B0 := B0) (Bf := Bf)
    (fun r hr => by rw [← node_ns hB0, hpre.1] at hr; cases hr; exact hrn0)
    (by rw [← node_ns hBf]; exact hrk) hpark hspk hpl (by rw [← node_ns hBf]; exact hrp) hpnull
    hroot0 rfl hK
  have hpo := tail_parOK hpre hsp hend hd hsr hL
  have hGf : spG Xf wf.wtxid (mapLen wf.ms) wf.fl := by
    rw [wtxid_of_C hL.step.1]; exact hL.step.2.2.2.1
  refine ⟨h + 1, [], pcSlots (spP Xf) ps, [pl], ⟨hrp, hGf, Or.inr ⟨hut,
    ⟨hpnull, Bf, hBf, ?_, ?_⟩, ?_, fun id hid => absurd hid List.not_mem_nil, hvc, ?_, ?_, hpo⟩⟩,
    ?_⟩
  · rw [hsimB.1]; exact hrootf
  · intro x hx hne
    rw [hsimB.1] at hx
    obtain ⟨rx, h1, h2⟩ := hchainf x hx hne
    exact ⟨rx, by rw [node_ns hBf]; exact h1, h2⟩
  · have hs := hL.slot; rw [hown] at hs; exact hs
  · intro y hy
    rw [hstA.1]; rw [hstA.2.1] at hy
    exact hfc0 y (applySteps_free_sub _ _ _ _ hy)
  · intro s hs
    rw [hstA.1] at hs
    exact Nat.lt_of_lt_of_le (htl0 s hs) hmk
  -- the new root's spill's success
  intro Xg wg st2 hdone
  obtain ⟨hstep2, hdone2⟩ := hdone
  rcases hdone2 with ⟨hs, -⟩ | ⟨-, T2, D', hfr2, hT2, hsl2, hDk2, hDn2, hPd2, hpo2, hroot2⟩
  · rw [hspl] at hs; cases hs
  have hplX : X.t.objs !! pl = none := tail_fresh hpre hsp hend hfr1
  -- through the new root's spill: a node but `pl`
  have hkf : ∀ l r1, Xf.node bl l = some r1 → l ≠ pl →
      ∃ r', Xg.node bl l = some r' ∧ nodeSim r1 r' := by
    intro l r1 hr1 hlp
    by_cases hl2 : l ∈ T2
    · rcases hT2 l hl2 with h0 | ⟨_, _, _, _, _, h0, -⟩ | ⟨-, -, hk⟩
      · rw [node_none_of_objs h0] at hr1; cases hr1
      · cases h0
      · exact hk r1 hr1
    · have hl : l ∉ [pl] ++ T2 := by
        simp only [List.mem_append, List.mem_singleton]
        rintro (e | e)
        · exact hlp e
        · exact hl2 e
      obtain ⟨r', hr', hs', -⟩ := spFrame_node hfr2 hr1 hl
      exact ⟨r', hr', hs'⟩
  have hkeep : ∀ l r, l ∉ N → X.node bl l = some r →
      ∃ r', Xg.node bl l = some r' ∧ nodeSim r r' := by
    intro l r hlN hr
    obtain ⟨r1, hr1, hs1⟩ := tail_kept hpre hsp hend hsr hL.frame (Or.inr hfr1) hlN hr
    have hlp : l ≠ pl := by
      intro e; subst e; rw [node_none_of_objs hplX] at hr; cases hr
    obtain ⟨r', hr', hs'⟩ := hkf l r1 hr1 hlp
    exact ⟨r', hr', nodeSim_trans hs1 hs'⟩
  refine ⟨spStep_trans hstA hstep2, Or.inr ⟨hsp,
    ((T0 ++ r'.cs.filter (fun c => decide (c ∉ N)) ++ (xs.drop 1).map (·.1) ++ [pl]) ++
      ([pl] ++ T2)).filter (fun l => decide (l ∉ N)), D', ?_, ?_, hsl2, ?_, ?_, ?_, hpo2, ?_⟩⟩
  · refine spFrame_mono (spFrame_trans hfrA hfr2) (fun l hl => ?_)
    by_cases hlN : l ∈ N
    · exact List.mem_append_left _ hlN
    · refine List.mem_append_right _ (List.mem_filter.2 ⟨?_, decide_eq_true hlN⟩)
      rcases List.mem_append.1 hl with hl | hl
      · rcases List.mem_append.1 hl with hl | hl
        · exact absurd hl hlN
        · exact List.mem_append_left _ hl
      · exact List.mem_append_right _ hl
  · intro l hl
    obtain ⟨hl, hlN⟩ := List.mem_filter.1 hl
    have hlN' : l ∉ N := of_decide_eq_true hlN
    rcases List.mem_append.1 hl with hl | hl
    · rcases List.mem_append.1 hl with hl | hl
      · rcases tail_T hpre hsp hend hsr l hl with h1 | ⟨-, h1⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inr ⟨rfl, h1, fun r hr => hkeep l r hlN' hr⟩)
      · rw [List.mem_singleton] at hl; subst hl; exact Or.inl hplX
    · rcases List.mem_append.1 hl with hl | hl
      · rw [List.mem_singleton] at hl; subst hl; exact Or.inl hplX
      · rcases hT2 l hl with h0 | ⟨_, _, _, _, _, h0, -⟩ | ⟨-, hlc, -⟩
        · exact Or.inl (spFrame_objs_none hfrA h0)
        · cases h0
        · rw [hcsP, xs_map_head hsr.head] at hlc
          rcases List.mem_cons.1 hlc with e | hlc
          · exact absurd (e ▸ hnN) hlN'
          · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hlc
            exact Or.inl (tail_fresh hpre hsp hend (hsr.fresh x hx))
  · intro s hs
    rcases hDk s hs with h1 | h1
    · exact hDk2 s h1
    · exact Or.inr (hstep2.2.2.2.2.2.1 s h1)
  · intro s hs
    rcases hDn2 s hs with h1 | h1
    · rcases hDn s h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (newSlot_mono h2 (fun x hx => List.mem_append_left _ hx) (Nat.le_refl _))
    · exact Or.inr (newSlot_mono h1 (fun x hx => List.mem_append_right _ hx) hmk)
  · intro x hx hxD
    by_cases hx1 : spP Xf !! x = spP X !! x
    · have hx2 : spP Xg !! x ≠ spP Xf !! x := by rw [hx1]; exact hx
      obtain ⟨-, hpend⟩ := hstep2.2.2.2.2.2.2.1 x hx2
      rcases hDk x hxD with h1 | h1
      · exact hPd2 x hx2 h1
      · exact hpend h1
    · exact hPd x hx1 hxD
  · obtain ⟨rt, rr, S, h', hrt, hrtl, hrts, hrtp, ⟨B', hB', hroot'⟩, hst, hD', hels⟩ := hroot2
    refine ⟨rt, rr, S, h', hrt, hrtl, hrts, hrtp, ⟨B', hB', ?_⟩, hst, hD', hels⟩
    have hnp : n ≠ pl := by
      intro e; have := hpre.1; rw [e, node_none_of_objs hplX] at this; cases this
    obtain ⟨rg, hrg, hsg⟩ := hkf n rk hrk hnp
    rw [node_ns hB'] at hrg
    have hpg' : rg.nv.parent' = pl := by rw [nodeSim_parent hsg, hpark]
    exact nodeRootIn.up n rt rg hrg (by rw [hpg']; exact hpl) (by rw [hpg']; exact hroot')

end lemmas

end Spill

end bbolt
end EtcdGrove
end Perennial
