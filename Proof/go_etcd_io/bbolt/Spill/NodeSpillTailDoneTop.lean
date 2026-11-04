/-
`node.spill`'s tail (U9z, `notes/bbolt-proof-plan.md`; pure): **the unsplit top node's `spDone`**
(`tail_done_top1`: no parent, one piece, `n` its own final root), given what `pcLoop` does not yet
carry (U9z's report): the slots' bookkeeping (`hDk`, `hDn`, `hPd`) and the piece's tree as an
`sTree` within `n`'s bounds (`hroot`: `pcLoop.done`'s `fTree` gives it for a non-empty piece; an
empty root leaf has none).
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

theorem derefPre_null {X : WX} (h : derefPre X) :
    ∀ bl B, X.t.bs !! bl = some B → B.ns !! null = none :=
  fun bl B hB => (h.2.2.1 bl B hB).2

/-- **The unsplit top node's `spDone`** (see the module doc). -/
theorem tail_done_top1 {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {X' : WX} {w' : WDb} {r' : NRec} {st0 : List FLStep} {T0 : List Loc}
    {X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {rp0 : NRec}
    {bs : List WEntry} {j : Nat} {Es : List (List El)} {Ds : List (List Nat)} {ps : List Piece}
    {Xf : WX} {wf : WDb} {stl : List FLStep}
    (hpre : spPre X w bl n rn O lo hi h F D N E .top) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st0 T0)
    (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss null rp0)
    (hEs : Es.flatten = E)
    (hL : pcLoop X' r' X2 w' bl O hi h xs wss null bs j Es Ds xs.length ps Xf wf stl)
    (hDk : ∀ s ∈ D, s ∈ pcSlots (spP Xf) ps ∨ s ∈ pendSlots wf.fl)
    (hDn : ∀ s ∈ pcSlots (spP Xf) ps, s ∈ D ∨ newSlot (st0 ++ stl) X.t.mv.pgid'.toNat s)
    (hPd : ∀ x, spP Xf !! x ≠ spP X !! x → x ∉ D)
    (hroot : ∀ p, ps[0]? = some p →
      sTree (spP Xf) Xf.t.mv.pgid'.toNat p.id.toNat lo hi h p.S) :
    spDone X Xf w wf bl n rn O lo hi h D N E .top (st0 ++ stl) := by
  -- one piece: `n`
  have hx1 : xs.length = 1 := by
    have hrN : r'.nilCh.nv.parent' = null := by
      obtain ⟨-, -, -, hnv, -⟩ := spEnd_rec hpre hsp hend
      show r'.nv.parent' = null; rw [hnv]
      rcases hpre.2.2 with ⟨hs, -⟩ | ⟨-, hctx, -⟩
      · rw [hsp] at hs; cases hs
      · exact hctx.1
    rcases hsr.par with ⟨-, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd rfl h1
    · exact absurd hrN h1
  obtain ⟨x0, hx0⟩ : ∃ x0, xs[0]? = some x0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hx1]; exact Nat.zero_lt_one)⟩
  have hx0n : x0.1 = n := by
    have := hsr.head; rw [List.head?_eq_getElem?, hx0] at this; simpa using this
  obtain ⟨p0, hp0⟩ : ∃ p0, ps[0]? = some p0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hL.len, hx1]; exact Nat.zero_lt_one)⟩
  obtain ⟨w0, hw0⟩ : ∃ w0, wss[0]? = some w0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hsr.len, hx1]; exact Nat.zero_lt_one)⟩
  have hps : ps = [p0] := by
    have hl : ps.length = 1 := by rw [hL.len, hx1]
    match ps, hl, hp0 with
    | [a], _, hp => simp at hp; rw [hp]
  have hEs1 : Es = [Es.getD 0 []] := by
    have hl : Es.length = 1 := by rw [hL.Elen, hx1]
    match Es, hl with
    | [a], _ => rfl
  obtain ⟨rk, hrk, hlv, -, hspl, -, -, hpar, hpg, -, -, -, hf⟩ := hL.done 0 x0 p0 w0 hx0 hp0 hw0
  rw [hx0n] at hrk hlv
  have hG := hL.step.2.2.2.1
  have hlen0 : xs.length ≠ 0 := by rw [hx1]; exact Nat.one_ne_zero
  refine ⟨tail_step hpre hend hsr hL.step, Or.inr ⟨hsp,
    T0 ++ r'.cs.filter (fun c => decide (c ∉ N)) ++ (xs.drop 1).map (·.1),
    pcSlots (spP Xf) ps, ?_, fun l hl => ?_, ?_, hDk, hDn, hPd, ?_⟩⟩
  · refine spFrame_drop_null (derefPre_null hpre.2.1.2.2.1) (derefPre_null hG.2.2.1) ?_
    have := tail_frame hpre hsp hend hsr hL.frame
    rw [← List.append_assoc] at this; exact this
  · rcases tail_T hpre hsp hend hsr l hl with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)
  · have hs := hL.slot
    have hD0 : Ds.drop xs.length = [] := List.drop_eq_nil_of_le (Nat.le_of_eq hL.Dlen)
    simp only [hlen0, ↓reduceIte, hD0, List.flatten_nil, List.nil_append] at hs
    exact hs
  · obtain ⟨B', hB', hrB⟩ := node_bs_of hrk
    refine ⟨n, rk, p0.S, h, hrk, hlv, hspl, hpar, ⟨B', hB', nodeRootIn.top n rk hrB hpar⟩, ?_,
      ?_, ?_⟩
    · rw [hpg]; exact hroot p0 hp0
    · rw [hps]; simp [pcSlots]
    · rw [hpg, hf.2.2, ← hEs, hEs1]; simp

end lemmas

end Spill

end bbolt
end EtcdGrove
end Perennial
