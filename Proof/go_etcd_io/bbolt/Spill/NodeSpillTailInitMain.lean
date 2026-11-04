/-
`node.spill` after its children's loop (U9w2, `notes/bbolt-proof-plan.md`; pure): **the pieces'
loop's invariant at its start** (`pcInv_init'`, after the split): the entries' families
(`tail_init_ents`), the parent (`tail_init_par`), the spill's global state across the kill and
the split (`spG_tailSplit`: `spG_nilCh`, then the split's `G`), the step and frame reflexive.

Open (a named `sorry`): `tail_nilChPre` (what `spG_nilCh` needs of `n`'s children after the
children's loop: the buckets' nodes disjoint, each child a childless non-root node of `bl`, no
other live node's child; `spEnd` does not carry them). The split's `G` premise is
`NodeSpillTailInitRoot.tail_rootN'`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitEnts
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitPar
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitNilCh
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInitRoot

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

/-- **What `spG_nilCh` needs of `n`'s children after the children's loop** (a `sorry`: `spEnd`
does not carry them; the leaf case has no children, but the buckets' disjointness is a heap
fact, `wtxW_heapOK`, which `spillTail_gen`'s `H1` does not pass). -/
theorem tail_nilChPre {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) {B : BRec}
    (hB : X'.t.bs !! bl = some B) :
    objsDisj X'.t ∧ (∀ c ∈ r'.cs, ∃ rc, B.ns !! c = some rc ∧ rc.cs = [] ∧ rc.nv.parent' ≠ null) ∧
      (∀ m rm, B.ns !! m = some rm → m ∈ X'.live → m ≠ n → ∀ c ∈ rm.cs, c ∉ r'.cs) := by
  sorry

/-- **The spill's global state after the kill and the split.** -/
theorem spG_tailSplit {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    {X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {pl : Loc}
    {rp' : NRec}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T)
    (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp') :
    spG X2 w'.wtxid (mapLen w'.ms) w'.fl := by
  have hst := spEnd_step hpre hend
  have hG' : spG X' w'.wtxid (mapLen w'.ms) w'.fl := by
    rw [wtxid_of_C hst.1]; exact hst.2.2.2.1
  obtain ⟨hn', -⟩ := spEnd_rec hpre hsp hend
  obtain ⟨B, hB, hnB⟩ := node_bs_of hn'
  obtain ⟨hd, hcs, hu⟩ := tail_nilChPre hpre hsp hend hB
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
    (X2 : WX) (xs : List (Loc × node × List Inode)) (wss : List (List WEntry)) (pl : Loc)
    (rp' : NRec) (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp')
    (hfit : ∀ x ∈ xs, pieceFits 4096 x.2.2 ∧ (2 ≤ xs.length → 2 ≤ x.2.2.length)) :
    pcInv X w bl n rn O lo hi h D N E cs xs pl 0 X2 w' st := by
  obtain ⟨Es, Ds, hEl, hDl, hEf, hents, hDk, hDn, hPd, hsl⟩ := tail_init_ents hpre hsp hend hsr
  obtain ⟨bs, j, hcs, hpar⟩ := tail_init_par hpre hsp hend hsr
  have hst := spEnd_step hpre hend
  have hG2 := spG_tailSplit hpre hsp hend hsr
  have hmv : X2.t.mv = X'.t.mv := hsr.same.1.trans (nilCh_mv _ _ _ _)
  have hP : spP X2 = spP X' := (split_spP hsr).trans (nilCh_spP _ _ _ _)
  refine ⟨X', w', r', st, T, X2, wss, rp', bs, j, Es, Ds, [], [], hend, hlens, hsr, hfit,
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
