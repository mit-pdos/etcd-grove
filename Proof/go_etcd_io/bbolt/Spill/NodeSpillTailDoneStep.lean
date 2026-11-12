/-
`node.spill`'s tail (U9z, `notes/bbolt-proof-plan.md`; pure): **the spill's step and frame from
its start to the pieces' loop's end**, composed from the children's loop's (`spEnd`), `n.children =
nil` (`spFrame_nilCh`), the split (`splitRel`) and the pieces' loop (`pcLoop.step`, `.frame`):
`tail_step`, `tail_frame` (the touched nodes: `N`, the children's loop's fresh ones, `n`'s old
children not in `N`, the split's fresh pieces and the parent), `tail_T` (those but the parent
fresh at the start, or `n`'s children in the top case) and `spFrame_drop_null`.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailDoneFrame

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

/-- A step from a state with the same page map, page cache and view. -/
theorem spStep_congr {X1 X1' X3 : WX} {w1 w3 : WDb} {O : List Nat} {st : List FLStep}
    (hP : spP X1' = spP X1) (hpm : X1'.t.pm = X1.t.pm) (hv : X1'.v.pages = X1.v.pages)
    (hb : X1'.t.bufs = X1.t.bufs) (hmv : X1'.t.mv = X1.t.mv)
    (h : spStep X1 X3 w1 w3 O st) : spStep X1' X3 w1 w3 O st := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k, k', k''⟩ := h
  refine ⟨a, b, c.trans hv.symm, d, e, f, fun x hx => g x (by rw [← hP]; exact hx),
    fun F hF hfr => i F hF (fun id hid => ?_), fun hok => j ?_,
    markGrow_congrL k hb (by rw [hmv]), srcGrow_congrL k' hb (by rw [hmv]), k''⟩
  · have := hfr id hid; rw [hpm] at this; exact this
  · unfold bufsOK at hok ⊢; rw [hb, hmv] at hok; exact hok

/-- The children's loop's step. -/
theorem spEnd_step {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st : List FLStep} {T : List Loc}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st T) : spStep X X' w w' O st := by
  rcases hend with ⟨-, rfl, rfl, -, rfl, -⟩ | ⟨-, h', es, i, -, hl, -⟩
  · exact spStep_refl O hpre.2.1 hpre.2.1.2.1
  · exact hl.step

theorem split_spP {X1 X2 : WX} {bl n : Loc} {rN : NRec} {xs : List (Loc × node × List Inode)}
    {wss : List (List WEntry)} {pl : Loc} {rp' : NRec}
    (hsr : splitRel X1 X2 bl n rN xs wss pl rp') : spP X2 = spP X1 := by
  unfold spP WX.bufPages; rw [hsr.same.2.1, hsr.same.2.2.2]

/-- **The step from the spill's start to the pieces' loop's end.** -/
theorem tail_step {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st0 : List FLStep} {T0 : List Loc}
    {X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {pl : Loc}
    {rp0 : NRec} {Xf : WX} {wf : WDb} {stl : List FLStep}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st0 T0)
    (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp0)
    (hst : spStep X2 Xf w' wf O stl) : spStep X Xf w wf O (st0 ++ stl) := by
  refine spStep_trans (spEnd_step hpre hend) (spStep_congr ?_ ?_ ?_ ?_ ?_ hst)
  · rw [split_spP hsr, nilCh_spP]
  · rw [hsr.same.2.2.1, nilCh_pm]
  · rw [hsr.same.2.2.2, nilCh_v]
  · rw [hsr.same.2.1, nilCh_bufs]
  · rw [hsr.same.1, nilCh_mv]

/-- A frame whose touched nodes include `null`, which no bucket's node is, is one without it. -/
theorem spFrame_drop_null {X X' : WX} {bl : Loc} {T : List Loc}
    (hX : ∀ bl B, X.t.bs !! bl = some B → B.ns !! null = none)
    (hX' : ∀ bl B, X'.t.bs !! bl = some B → B.ns !! null = none)
    (h : spFrame X X' bl (T ++ [null])) : spFrame X X' bl T := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q, z⟩ := h
  have hm : ∀ y, y ∉ T → y ≠ null → y ∉ T ++ [null] := fun y h1 h2 hm =>
    (List.mem_append.1 hm).elim h1 (fun h3 => h2 (List.mem_singleton.1 h3))
  refine ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, fun B hB => ?_, fun y bl' B hB hs hy => ?_, q,
    fun bl' B B' y r r' hB hB' hr hr' hT hlv hv => ?_⟩
  · obtain ⟨B', hB', hs, hns⟩ := o B hB
    refine ⟨B', hB', hs, fun y hy => ?_⟩
    by_cases yn : y = null
    · subst yn; rw [hX _ _ hB, hX' _ _ hB']; trivial
    · exact hns y (hm y hy yn)
  · by_cases yn : y = null
    · subst yn; rw [hX _ _ hB] at hs; cases hs
    · exact p y bl' B hB hs (fun he => hm y (hy he) yn)
  · by_cases yn : y = null
    · subst yn; rw [hX _ _ hB] at hr; cases hr
    · exact z bl' B B' y r r' hB hB' hr hr' (fun he => hm y (hT he) yn) hlv hv

theorem xs_map_head {xs : List (Loc × node × List Inode)} {n : Loc}
    (hhd : (xs.head?.map (·.1)) = some n) : xs.map (·.1) = n :: (xs.drop 1).map (·.1) := by
  cases xs with
  | nil => cases hhd
  | cons a t => simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhd; simp [hhd]

/-- **The frame from the spill's start to the pieces' loop's end.** -/
theorem tail_frame {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st0 : List FLStep} {T0 : List Loc}
    {X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {pl : Loc}
    {rp0 : NRec} {Xf : WX}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st0 T0)
    (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp0)
    (hfr : spFrame X2 Xf bl (xs.map (·.1) ++ [pl])) (hd : objsDisj X'.t) :
    spFrame X Xf bl (N ++ (T0 ++ r'.cs.filter (fun c => decide (c ∉ N)) ++
      (xs.drop 1).map (·.1) ++ [pl])) := by
  obtain ⟨hn', -, -, -, -, -, hfr0, -⟩ := spEnd_rec hpre hsp hend
  have hnN : n ∈ N := by
    rcases hpre.2.2 with ⟨hs, -⟩ | ⟨hut, -⟩
    · rw [hsp] at hs; cases hs
    · exact uTree_head hut
  have hcs : ∀ c ∈ r'.cs, ∀ bl' B, X'.t.bs !! bl' = some B → (B.ns !! c).isSome → bl' = bl := by
    obtain ⟨-, hlv', -⟩ := spEnd_rec hpre hsp hend
    obtain ⟨B', hB', hr'⟩ := node_bs_of hn'
    have hdp := (spEnd_step hpre hend).2.2.2.1.2.2.1
    exact nilCh_cs_only hd fun c hc => ⟨B', hB', ((hdp.1 bl B' n r' hB' hr' hlv').2.2.2 c hc).2⟩
  have hall := spFrame_trans (spFrame_trans (spFrame_trans hfr0 (spFrame_nilCh hn' hcs)) hsr.frame) hfr
  refine spFrame_mono hall (fun l hl => ?_)
  rw [xs_map_head hsr.head] at hl
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hl
  by_cases hlN : l ∈ N
  · exact List.mem_append_left _ hlN
  · have key : l ∈ T0 ∨ l ∈ r'.cs ∨ l ∈ (xs.drop 1).map (·.1) ∨ l = pl := by
      rcases hl with (((h1 | h1) | h1 | h1) | (h1 | h1) | h1) | (h1 | h1) | h1
      · exact absurd h1 hlN
      · exact Or.inl h1
      · subst h1; exact absurd hnN hlN
      · exact Or.inr (Or.inl h1)
      · subst h1; exact absurd hnN hlN
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr h1))
      · subst h1; exact absurd hnN hlN
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr h1))
    refine List.mem_append_right _ ?_
    rcases key with h1 | h1 | h1 | h1
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h1))
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_filter.2 ⟨h1, decide_eq_true hlN⟩)))
    · exact List.mem_append_left _ (List.mem_append_right _ h1)
    · exact List.mem_append_right _ (List.mem_singleton.2 h1)

/-- The parent through the frames: fresh at the start in the top case. -/
theorem tail_fresh {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st0 : List FLStep} {T0 : List Loc}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st0 T0) {l : Loc}
    (h1 : (X'.nilCh bl n r').t.objs !! l = none) : X.t.objs !! l = none := by
  obtain ⟨hn', -, -, -, -, -, hfr0, -⟩ := spEnd_rec hpre hsp hend
  exact spFrame_objs_none hfr0 (nilCh_objs_none hn' h1)

/-- **The touched nodes but `N` and the parent**: fresh at the start, or (top case) `n`'s
children. -/
theorem tail_T {X : WX} {w : WDb} {bl n : Loc} {rn : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    {cs : SpCase} {X' : WX} {w' : WDb} {r' : NRec} {st0 : List FLStep} {T0 : List Loc}
    {X2 : WX} {xs : List (Loc × node × List Inode)} {wss : List (List WEntry)} {pl : Loc}
    {rp0 : NRec}
    (hpre : spPre X w bl n rn O lo hi h F D N E cs) (hsp : rn.nv.spilled' = false)
    (hend : spEnd X w bl n rn O lo hi h D N E X' w' r' st0 T0)
    (hsr : splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp0) :
    ∀ l ∈ T0 ++ r'.cs.filter (fun c => decide (c ∉ N)) ++ (xs.drop 1).map (·.1),
      X.t.objs !! l = none ∨ (cs = .top ∧ l ∈ rn.cs) := by
  obtain ⟨-, -, -, -, -, hcs', -, hT⟩ := spEnd_rec hpre hsp hend
  intro l hl
  simp only [List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_map] at hl
  rcases hl with (hl | ⟨hl, hlN⟩) | ⟨x, hx, rfl⟩
  · exact Or.inl (hT l hl)
  · rcases hcs' l hl with hl | hl
    · cases cs with
      | top => exact Or.inr ⟨rfl, hl⟩
      | child pl rp j plo phi =>
        rcases hpre.2.2 with ⟨hs, -⟩ | ⟨-, hctx, -⟩
        · rw [hsp] at hs; cases hs
        · exact absurd (hctx.2.2.2.2.2.2.2.2.2.2.2.2.1 l hl) hlN
    · exact Or.inl hl
  · exact Or.inl (tail_fresh hpre hsp hend (hsr.fresh x hx))

end lemmas

end Spill

end bbolt
end EtcdGrove
end Perennial
