/-
`node.spill` after its children's loop (U9w2, `notes/bbolt-proof-plan.md`; pure): **the pieces'
loop's invariant at its start** (`pcInv_init'`, after the split): the entries' families
(`tail_init_ents`), the parent (`tail_init_par`), the spill's global state across the kill and
the split (`spG_tailSplit`: `spG_nilCh`, then the split's `G`), the step and frame reflexive.

`tail_nilChPre` (U9w3: what `spG_nilCh` needs of `n`'s children after the children's loop: the
buckets' nodes disjoint, from the heap, each child a childless node of `bl` whose parent is `n`,
no other live node's child, from the loop's `parOK`, `Spill/ParOKBase.parOK_uniq`). The split's
`G` premise is `NodeSpillTailInitRoot.tail_rootN'`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitEnts
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitPar
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitNilCh
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitRoot
public import Proof.go_etcd_io.bbolt.Spill.ParOKBase

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section init
variable [GooseExts] [GoGlobalContext]

/-- **What `spG_nilCh` needs of `n`'s children after the children's loop** (the buckets'
disjointness is the heap's, `wtxW_heapOK`, passed by `spillTail_gen`'s `H1`; a leaf has no
children; a branch's children are spilled, `spilledN`, and the parent pointers, `parOK`, are the
loop's). -/
theorem tail_nilChPre {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) (hd : objsDisj X'.t) {B : BRec}
    (hB : X'.t.bs !! bl = some B) :
    objsDisj X'.t ∧ (∀ c ∈ r'.cs, ∃ rc, B.ns !! c = some rc ∧ rc.cs = [] ∧ rc.nv.parent' ≠ null) ∧
      (∀ m rm, B.ns !! m = some rm → m ∈ X'.live → m ≠ n → ∀ c ∈ rm.cs, c ∉ r'.cs) := by
  obtain ⟨hn', hlv', -⟩ := spEnd_rec hpre hsp hend
  have hG' := (spEnd_step hpre hend).2.2.2.1
  have hnn : n ≠ null := by
    intro e; rw [e] at hn'
    obtain ⟨B0, hB0, h0⟩ := node_bs_of hn'
    rw [(hG'.2.2.1.2.2.1 bl B0 hB0).2] at h0; cases h0
  have hnode : ∀ l, X'.node bl l = B.ns !! l := fun l => by unfold WX.node; rw [hB]; rfl
  have hu := hpre.2.2.resolve_left (fun h0 => by rw [hsp] at h0; cases h0.1)
  obtain ⟨hut, -, -, -, -, -, -, hpar0⟩ := hu
  have key : parOK X' bl ∧ ∀ c ∈ r'.cs, ∃ rc, X'.node bl c = some rc ∧ rc.cs = [] := by
    rcases hend with ⟨hleaf, rfl, rfl, rfl, rfl, rfl⟩ | ⟨-, h', es, i, -, hl, hlen, -⟩
    · refine ⟨hpar0, fun c hc => ?_⟩
      cases hut with
      | leaf _ r _ _ _ hr _ _ hcs =>
        rw [hpre.1] at hr; cases hr; rw [hcs] at hc; cases hc
      | branch _ r _ _ _ _ hr _ hl' =>
        rw [hpre.1] at hr; cases hr; rw [hleaf] at hl'; cases hl'
    · refine ⟨hl.par, fun c hc => ?_⟩
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hc
      have hkl := (List.getElem?_eq_some_iff.1 hk).1
      obtain ⟨-, rc, hrc, -, -, hcs, -⟩ := hl.done k c (by omega) hk
      exact ⟨rc, hrc, hcs⟩
  obtain ⟨hpar, hcs⟩ := key
  obtain ⟨hP1, hP2⟩ := parOK_uniq hpar hn' hlv'
  refine ⟨hd, fun c hc => ?_, fun m rm hm hmlv hne c hc =>
    hP2 m rm (by rw [hnode]; exact hm) hmlv hne c hc⟩
  obtain ⟨rc, hrc, hc0⟩ := hcs c hc
  obtain ⟨rc', hrc', hp⟩ := hP1 c hc
  rw [hrc] at hrc'; cases hrc'
  exact ⟨rc, by rw [← hnode]; exact hrc, hc0, by rw [hp]; exact hnn⟩

/-- **The spill's global state after the kill and the split.** -/
theorem spG_tailSplit {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    {X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {pl : Loc}
    {rp' : NRec}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) (hd : objsDisj X'.t)
    (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp') :
    spG X2 w'.wtxid (mapLen w'.ms) w'.fl := by
  have hst := spEnd_step hpre hend
  have hG' : spG X' w'.wtxid (mapLen w'.ms) w'.fl := by
    rw [wtxid_of_C hst.1]; exact hst.2.2.2.1
  obtain ⟨hn', -⟩ := spEnd_rec hpre hsp hend
  obtain ⟨B, hB, hnB⟩ := node_bs_of hn'
  obtain ⟨hd, hcs, hu⟩ := tail_nilChPre hpre hsp hend hd hB
  exact hsr.G (fun h0 _ => tail_rootN' hpre hsp hend h0) _ _ _ (spG_nilCh hB hnB hd hcs hu hG')

theorem pcOwn_zero (X' : WX) (r' : NRec) (Ds : List (List Nat)) (Xi : WX) :
    pcOwn X' r' Ds 0 [] Xi = ownSl X'.v r'.nv.pgid' ++ Ds.flatten := by
  simp [pcOwn, pcSlots]

/-- **The invariant at the loop's start**, after the split (the statement of the stub it replaced,
`NodeSpillTailInv.pcInv_init`). -/
theorem pcInv_init' {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) (hlens : insLens r'.ins r'.ws)
    (hd : objsDisj X'.t) (X2 : WX) (xs : List (Loc × node × List Inode)) (wss : List (List WEntry)) (pl : Loc)
    (rp' : NRec) (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp')
    (hfit : ∀ x ∈ xs, pieceFits 4096 x.2.2 ∧ (2 ≤ xs.length → 2 ≤ x.2.2.length)) :
    pcInv X w bl n rn O lo hi h D N E cs xs pl 0 X2 w' st := by
  obtain ⟨Es, Ds, hEl, hDl, hEf, hents, hDk, hDn, hPd, hsl⟩ := tail_init_ents hpre hsp hend hsr
  obtain ⟨bs, j, hcs, hpar⟩ := tail_init_par hpre hsp hend hsr
  have hst := spEnd_step hpre hend
  have hG2 := spG_tailSplit hpre hsp hend hd hsr
  have hmv : X2.t.mv = X'.t.mv := hsr.same.1.trans (nilCh_mv _ _ _ _)
  have hP : spP X2 = spP X' := (split_spP hsr).trans (nilCh_spP _ _ _ _)
  refine ⟨X', w', r', st, T, X2, wss, rp', bs, j, Es, Ds, [], [], hend, hlens, hd, hsr, hfit,
    (List.append_nil st).symm, hEf, hents, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [pcOwn_zero]; exact hDk
  · rw [pcOwn_zero]; exact hDn
  · rw [hP]; exact hPd
  · revert hcs; cases cs <;> exact id
  exact {
    len := rfl
    start := fun _ => ⟨rfl, rfl, rfl⟩
    vb := hG2.2.2.2.2.2.2.2.2.1
    ile := Nat.zero_le _
    pcl := fun k p x hp => by simp at hp
    Elen := hEl
    Dlen := hDl
    step := spStep_refl O hG2 (by rw [hmv]; exact hst.2.2.2.2.1)
    frame := spFrame_refl _ _ _
    todo := fun k x ws _ hx hws => by
      obtain ⟨h1, h2, -⟩ := hsr.prec k x ws hx hws
      exact ⟨_, h1, h2, nodeSim_refl _⟩
    done := fun k x p ws _ hp => by simp at hp
    slot := by rw [pcOwn_zero, hmv]; exact hsl
    agree := fun x hx => absurd (by rw [hP]) hx
    par := hpar }

end init

end Spill

end bbolt
end EtcdGrove
end Perennial
