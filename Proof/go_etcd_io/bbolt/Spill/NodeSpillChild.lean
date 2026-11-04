/-
`node.spill`'s children's loop (U9j, `notes/bbolt-proof-plan.md`; pure): **an unspilled child's
step** (`spLoop_child`): from the loop's invariant at child `i` (entry `j`'s unspilled child `c`)
and the child's `spDone`, the invariant at `i + 1` (over `ChildStep.uBr_childStep`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillLoop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section child
variable [GooseExts]

/-- **An unspilled child's spill** (entry `j`'s child `c`, the loop's child `i`), its `spDone`
from `(X', w')` to `(X'', w'')`: the invariant at the next index (the child's pieces in `n`'s
entries; the child's touched fresh nodes, but `n` itself, added to the loop's). -/
theorem spLoop_child {X : WX} {w : WDb} {bl n : Loc} {r : NRec} {O : List Nat}
    {lo hi : Option (List w8)} {h : Nat} {D0 : List Nat} {N0 : List Loc} {E0 : List El}
    {X' : WX} {w' : WDb} {r' : NRec} {es : List UE} {i : Nat} {st : List FLStep}
    {T : List Loc} {c : Loc} {rc : NRec} {j : Nat} {Fc Dc : List Nat} {Nc : List Loc}
    {Ec : List El} {X'' : WX} {w'' : WDb} {st' : List FLStep}
    (hl : spLoop X w bl n r O lo hi h D0 N0 E0 X' w' r' es i st T)
    (hc : r'.cs[i]? = some c) (hj : es[j]? = some ⟨some c, Fc, Dc, Nc, Ec⟩)
    (hsp : rc.nv.spilled' = false)
    (hdone : spDone X' X'' w' w'' bl c rc (chO O X'.v r' es j) (childLo lo (wKey r'.ws) j)
      (childHi hi (wKey r'.ws) r'.ws.length j) h Dc Nc Ec (.child n r' j lo hi) st') :
    ∃ r'' es' T', spLoop X w bl n r O lo hi h D0 N0 E0 X'' w'' r'' es' (i + 1) (st ++ st') T' := by
  have htx : w'.wtxid = w.wtxid := wtxid_of_C hl.step.1
  have hfree' : spFree X' w'.fl w'.wtxid (ownF r'.nv.pgid' ++ es.flatMap UE.F) := by
    rw [htx]; exact hl.free
  obtain ⟨r'', ps, hr'', hcs'', hpg'', hlive'', hbr, hsl, hfr, hstep, hpar, hhd, hps, hE,
    ⟨Tc, hfrc, hTc⟩, hDk, hDn, hPd⟩ :=
    uBr_childStep (O := O) hl.br hj hl.step.2.2.2.1.2.2.1 hl.live hsp hfree' hdone
  have hil : i < r'.cs.length := (List.getElem?_eq_some_iff.1 hc).1
  have hjes : j < es.length := (List.getElem?_eq_some_iff.1 hj).1
  have hjw : j < r'.ws.length := by rw [← hl.br.len]; exact hjes
  have hent := hl.br.ent j _ _ (List.getElem?_eq_getElem hjw) hj
  have hNc : ∀ l ∈ Nc, l ∈ N0 := fun l hl' =>
    hl.NN l (List.mem_flatMap.2 ⟨_, mem_of_get hj, hl'⟩)
  have hes : es.flatMap UE.D =
      (es.take j).flatMap UE.D ++ Dc ++ (es.drop (j + 1)).flatMap UE.D := flatMap_split UE.D hj
  have hpages : X''.v.pages = X'.v.pages := hstep.2.2.1
  -- the children before `i + 1` spilled
  have hdone' : ∀ k c', k < i + 1 → r''.cs[k]? = some c' → spilledN X'' bl c' := by
    intro k c' hk hc'
    have hk' : r'.cs[k]? = some c' := by
      rw [hcs'', List.getElem?_append_left (by omega)] at hc'; exact hc'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
    · have hs := hl.done k c' hk hk'
      refine spilledN_frame hfrc hs ?_
      intro hm
      rcases List.mem_append.1 hm with hm | hm
      · obtain ⟨r0, h0, hs0⟩ := uEnt_N_node hent c' hm
        exact not_spilledN_of h0 hs0 hs
      · rcases hTc c' hm with h0 | h0
        · obtain ⟨_, rc0, hrc0, _⟩ := hs
          have := node_objs hrc0; rw [h0] at this; cases this
        · subst h0; exact not_spilledN_of hl.br.node hl.br.un.2.2.1 hs
    · subst hk
      rw [hc] at hk'; cases hk'
      cases ps with
      | nil => cases hhd
      | cons x ps' =>
        simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhd
        rw [← hhd]; exact piece_spilledN hps List.mem_cons_self
  -- the frame
  have hframe : spFrame X X'' bl (N0 ++ (T ++ Tc.filter (· ≠ n))) := by
    refine spFrame_mono (spFrame_trans hl.frame hfrc) (fun l hm => ?_)
    simp only [List.mem_append] at hm ⊢
    rcases hm with (h1 | h1) | (h1 | h1)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inl (hNc l h1)
    · by_cases e : l = n
      · subst e; exact Or.inl hl.nN
      · exact Or.inr (Or.inr (List.mem_filter.2 ⟨h1, by simp [e]⟩))
  have hfresh : ∀ l ∈ T ++ Tc.filter (· ≠ n), X.t.objs !! l = none := by
    intro l hm
    rcases List.mem_append.1 hm with h1 | h1
    · exact hl.fresh l h1
    · obtain ⟨h1, hne⟩ := List.mem_filter.1 h1
      rcases hTc l h1 with h0 | h0
      · cases hx : X.t.objs !! l with
        | none => rfl
        | some _ =>
          have := hl.frame.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 l (by simp [hx])
          rw [h0] at this; cases this
      · simp [h0] at hne
  have hEE : (es.take j ++ ps.map (pcUE (spP X'')) ++ es.drop (j + 1)).flatMap UE.E = E0 := by
    rw [← hl.EE, flatMap_split UE.E hj]
    simp only [List.flatMap_append]
    congr 2
    rw [← hE]
    simp [pcUE, List.flatMap_map]
  have hNN : ∀ l ∈ (es.take j ++ ps.map (pcUE (spP X'')) ++ es.drop (j + 1)).flatMap UE.N,
      l ∈ N0 := by
    intro l hm
    simp only [List.flatMap_append, List.mem_append] at hm
    rcases hm with (h1 | h1) | h1
    · obtain ⟨e, he, hle⟩ := List.mem_flatMap.1 h1
      exact hl.NN l (List.mem_flatMap.2 ⟨e, List.mem_of_mem_take he, hle⟩)
    · simp [pcUE, List.flatMap_map] at h1
    · obtain ⟨e, he, hle⟩ := List.mem_flatMap.1 h1
      exact hl.NN l (List.mem_flatMap.2 ⟨e, List.mem_of_mem_drop he, hle⟩)
  have hpend : ∀ s, s ∈ pendSlots w'.fl → s ∈ pendSlots w''.fl := hstep.2.2.2.2.2.1
  have hDk' : ∀ s ∈ D0, s ∈ ownSl X''.v r''.nv.pgid' ++
      (es.take j ++ ps.map (pcUE (spP X'')) ++ es.drop (j + 1)).flatMap UE.D ∨
      s ∈ pendSlots w''.fl := by
    intro s hs
    rw [hpg'', ownSl_congr hpages, List.flatMap_append, List.flatMap_append, pcUE_D]
    rcases hl.Dk s hs with h1 | h1
    · rw [hes] at h1
      simp only [List.mem_append] at h1 ⊢
      rcases h1 with h1 | ((h1 | h1) | h1)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr (Or.inl (Or.inl h1)))
      · rcases hDk s h1 with h2 | h2
        · exact Or.inl (Or.inr (Or.inl (Or.inr h2)))
        · exact Or.inr h2
      · exact Or.inl (Or.inr (Or.inr h1))
    · exact Or.inr (hpend s h1)
  have hDn' : ∀ s ∈ ownSl X''.v r''.nv.pgid' ++
      (es.take j ++ ps.map (pcUE (spP X'')) ++ es.drop (j + 1)).flatMap UE.D,
      s ∈ D0 ∨ newSlot (st ++ st') X.t.mv.pgid'.toNat s := by
    intro s hs
    rw [hpg'', ownSl_congr hpages, List.flatMap_append, List.flatMap_append, pcUE_D] at hs
    have hold : ∀ s ∈ ownSl X'.v r'.nv.pgid' ++ es.flatMap UE.D,
        s ∈ D0 ∨ newSlot (st ++ st') X.t.mv.pgid'.toNat s := fun s hs =>
      (hl.Dn s hs).imp_right fun h => newSlot_mono h (fun x hx => List.mem_append_left _ hx)
        (Nat.le_refl _)
    simp only [List.mem_append] at hs
    rcases hs with h1 | ((h1 | h1) | h1)
    · exact hold s (List.mem_append_left _ h1)
    · exact hold s (List.mem_append_right _ (by rw [hes]; simp [h1]))
    · rcases hDn s h1 with h2 | h2
      · exact hold s (List.mem_append_right _ (by rw [hes]; simp [h2]))
      · exact Or.inr (newSlot_mono h2 (fun x hx => List.mem_append_right _ hx)
          hl.frame.2.2.2.2.2.2.2.2.1)
    · exact hold s (List.mem_append_right _ (by rw [hes]; simp [h1]))
  have hPd' : ∀ x, spP X'' !! x ≠ spP X !! x → x ∉ D0 := by
    intro x hx hxD
    by_cases h1 : spP X' !! x = spP X !! x
    · have hne : spP X'' !! x ≠ spP X' !! x := by rw [h1]; exact hx
      obtain ⟨hO, hpd⟩ := hstep.2.2.2.2.2.2.1 x hne
      have hxc := hPd x hne
      rcases hl.Dk x hxD with h2 | h2
      · rw [hes] at h2
        simp only [List.mem_append] at h2
        rcases h2 with h2 | ((h2 | h2) | h2)
        · exact hO (List.mem_append_left _ (List.mem_append_right _ h2))
        · exact hO (List.mem_append_right _
            (by rw [List.flatMap_append]; exact List.mem_append_left _ h2))
        · exact hxc h2
        · exact hO (List.mem_append_right _
            (by rw [List.flatMap_append]; exact List.mem_append_right _ h2))
      · exact hpd h2
    · exact hl.Pd x h1 hxD
  refine ⟨r'', es.take j ++ ps.map (pcUE (spP X'')) ++ es.drop (j + 1), T ++ Tc.filter (· ≠ n),
    { br := hbr
      ile := by rw [hcs'', List.length_append]; omega
      done := hdone'
      slot := hsl
      free := by rw [← htx]; exact hfr
      step := spStep_trans hl.step (spStep_mono hstep fun x hx =>
        List.mem_append_left _ (List.mem_append_left _ hx))
      frame := hframe
      fresh := hfresh
      EE := hEE
      nN := hl.nN
      NN := hNN
      Dk := hDk'
      Dn := hDn'
      Pd := hPd'
      nv := hpar.2.2.1.trans (by rw [hl.nv])
      knil := hpar.2.2.2.1.trans hl.knil
      key := hpar.2.2.2.2.1.trans hl.key
      cap := hpar.2.2.2.2.2.1.trans hl.cap
      live := hlive'' }⟩

end child

end Spill

end bbolt
end EtcdGrove
end Perennial
