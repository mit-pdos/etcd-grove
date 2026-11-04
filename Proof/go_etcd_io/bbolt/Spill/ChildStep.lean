/-
The spill's pure facts (U9f, `notes/bbolt-proof-plan.md`): **a step of `node.spill`'s children's
loop** (`uBr_childStep`): from the parent's branch facts and the child's `spDone` (child case), the
parent's branch facts after (`uBr_replace`), its slots owned and its base pages freeable.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTreeReplace2
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSObjs
public import Proof.go_etcd_io.bbolt.Spill.SlotInv

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section step
variable [GooseExts]

theorem uEnt_F_D {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {ws : List WEntry} {cs : List Loc} {h i : Nat} {w : WEntry}
    {e : UE} (he : uEnt X bl P hwm n lo hi ws cs h i w e) : ∀ x ∈ e.F, x ∈ e.D := by
  cases he with
  | child _ _ _ _ _ _ _ _ c rc F D N E _ _ _ _ _ _ _ hut => exact uTree_F_D hut
  | fin => intro x hx; simp at hx

theorem node_objs {X : WX} {bl l : Loc} {r : NRec} (h : X.node bl l = some r) :
    (X.t.objs !! l).isSome = true := by
  unfold WX.node at h
  cases hb : X.t.bs !! bl with
  | none => rw [hb] at h; cases h
  | some B =>
    rw [hb] at h
    exact (objs_isSome X.t l).2 (Or.inr ⟨bl, B, hb, by simp only [Option.bind_some] at h; simp [h]⟩)

theorem node_none_of_objs {X : WX} {bl l : Loc} (h : X.t.objs !! l = none) : X.node bl l = none := by
  cases hn : X.node bl l with
  | none => rfl
  | some r => have := node_objs hn; rw [h] at this; cases this

/-- The other entries (all but `j`) by index. -/
theorem mem_others {α : Type} {es : List α} {j k : Nat} {e : α} (hk : k ≠ j) (he : es[k]? = some e) :
    e ∈ es.take j ++ es.drop (j + 1) := by
  rcases Nat.lt_or_gt_of_ne hk with h | h
  · exact List.mem_append_left _ (List.mem_of_getElem? (i := k)
      (by rw [List.getElem?_take_of_lt h]; exact he))
  · refine List.mem_append_right _ (List.mem_of_getElem? (i := k - (j + 1)) ?_)
    rw [List.getElem?_drop, show j + 1 + (k - (j + 1)) = k by omega]; exact he

theorem pcUE_D (P : Pages) (ps : List Piece) : (ps.map (pcUE P)).flatMap UE.D = pcSlots P ps := by
  simp [pcUE, pcSlots, List.flatMap_map]

theorem pcUE_F (P : Pages) (ps : List Piece) : (ps.map (pcUE P)).flatMap UE.F = [] := by
  simp [pcUE]

/-- **A step of the children's loop** (see the module doc): the parent `n` (record `r`, branch
facts at `X` over `es`), its entry `j` the unspilled child `c` (record `rc`), spilled from `(X, w)`
to `(X', w')` with the other slots `O`, `n`'s own and the other entries' owned. -/
theorem uBr_childStep {X X' : WX} {w w' : WDb} {bl n c : Loc} {r rc : NRec}
    {lo hi : Option (List w8)} {h : Nat} {es : List UE} {j : Nat} {Fc Dc : List Nat}
    {Nc : List Loc} {Ec : List El} {O : List Nat} {st : List FLStep}
    (hb : uBr X bl (spP X) X.t.mv.pgid'.toNat n r lo hi h es)
    (hj : es[j]? = some ⟨some c, Fc, Dc, Nc, Ec⟩) (hdp : derefPre X) (hnl : n ∈ X.live)
    (hsp : rc.nv.spilled' = false)
    (hfree : spFree X w.fl w.wtxid (ownF r.nv.pgid' ++ es.flatMap UE.F))
    (hdone : spDone X X' w w' bl c rc
      (O ++ ownSl X.v r.nv.pgid' ++ (es.take j ++ es.drop (j + 1)).flatMap UE.D)
      (childLo lo (wKey r.ws) j) (childHi hi (wKey r.ws) r.ws.length j) h Dc Nc Ec
      (.child n r j lo hi) st) :
    ∃ (r' : NRec) (ps : List Piece), X'.node bl n = some r' ∧ r'.cs = r.cs ++ (ps.drop 1).map Piece.l ∧
      r'.nv.pgid' = r.nv.pgid' ∧ n ∈ X'.live ∧
      uBr X' bl (spP X') X'.t.mv.pgid'.toNat n r' lo hi h
        (es.take j ++ ps.map (pcUE (spP X')) ++ es.drop (j + 1)) ∧
      slotInv w'.fl X'.t.mv.pgid'.toNat (O ++ (ownSl X'.v r'.nv.pgid' ++
        (es.take j ++ ps.map (pcUE (spP X')) ++ es.drop (j + 1)).flatMap UE.D)) ∧
      spFree X' w'.fl w.wtxid (ownF r'.nv.pgid' ++
        (es.take j ++ ps.map (pcUE (spP X')) ++ es.drop (j + 1)).flatMap UE.F) ∧
      spStep X X' w w'
        (O ++ ownSl X.v r.nv.pgid' ++ (es.take j ++ es.drop (j + 1)).flatMap UE.D) st ∧
      parentSpilled r r' j ps ∧ (ps.head?.map Piece.l) = some c ∧
      piecesOK X' bl n (spP X') X'.t.mv.pgid'.toNat (childLo lo (wKey r.ws) j)
        (childHi hi (wKey r.ws) r.ws.length j) h ps ∧
      ps.flatMap (fun x => treeEls (spP X') x.id.toNat) = Ec ∧
      (∃ Tc, spFrame X X' bl (Nc ++ Tc) ∧ ∀ l ∈ Tc, X.t.objs !! l = none ∨ l = n) ∧
      (∀ s ∈ Dc, s ∈ pcSlots (spP X') ps ∨ s ∈ pendSlots w'.fl) ∧
      (∀ s ∈ pcSlots (spP X') ps, s ∈ Dc ∨ newSlot st X.t.mv.pgid'.toNat s) ∧
      (∀ x, spP X' !! x ≠ spP X !! x → x ∉ Dc) ∧ (∀ x ∈ ps.drop 1, X.t.objs !! x.l = none) := by
  obtain ⟨hstep, hcase⟩ := hdone
  rcases hcase with ⟨hsp', -, -⟩ | ⟨-, T, D', hfr, hT, hsl, hDk, hDn, hPd, -, rest⟩
  · rw [hsp] at hsp'; cases hsp'
  obtain ⟨ps, r', hps, hhd, hfr1, hD', hE, hr', hpar, hlive⟩ := rest
  have hjes : j < es.length := (List.getElem?_eq_some_iff.1 hj).1
  have hpg : r'.nv.pgid' = r.nv.pgid' := by rw [hpar.2.2.1]
  -- the others' slots are in the frame
  have hOth : ∀ k e, k ≠ j → es[k]? = some e → ∀ x ∈ e.D,
      x ∈ O ++ ownSl X.v r.nv.pgid' ++ (es.take j ++ es.drop (j + 1)).flatMap UE.D :=
    fun k e hk he x hx => List.mem_append_right _ (List.mem_flatMap.2 ⟨e, mem_others hk he, hx⟩)
  have hB := hb.node
  unfold WX.node at hB
  obtain ⟨B, hBb, hBn⟩ : ∃ B, X.t.bs !! bl = some B ∧ B.ns !! n = some r := by
    cases hbb : X.t.bs !! bl with
    | none => rw [hbb] at hB; cases hB
    | some B => rw [hbb] at hB; exact ⟨B, rfl, hB⟩
  have hbr := uBr_replace (P := spP X) (P' := spP X') hb hj hfr
    (hfr.2.2.2.2.2.2.2.2.1)
    (fun l hl => by
      rcases List.mem_append.1 hl with hl | hl
      · exact Or.inl hl
      · rcases hT l hl with h0 | ⟨pl, rp, j', plo, phi, hcs, rfl⟩ | ⟨hcs, -⟩
        · exact Or.inr (Or.inl (node_none_of_objs h0))
        · cases hcs; exact Or.inr (Or.inr rfl)
        · cases hcs)
    (fun k e hk he x hx => Classical.byContradiction fun hne =>
      (hstep.2.2.2.2.2.2.1 x hne).1 (hOth k e hk he x hx))
    hps hhd hr' hpar hlive
    (fun x hx hmem => by
      have h1 := (hdp.1 bl B n r hBb hBn hnl).2.2.2 _ hmem
      have h2 := node_objs (X := X) (bl := bl) (l := x.l) (r := (B.ns !! x.l).get h1.2)
        (by unfold WX.node; rw [hBb]; simp)
      rw [hfr1 x hx] at h2; cases h2)
    (fun x hx => by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h1, h2, _⟩ := hps.2.2 i x hi
      exact ⟨h1, h2⟩)
  have hT' : ∀ l ∈ T, X.t.objs !! l = none ∨ l = n := by
    intro l hl
    rcases hT l hl with h0 | ⟨pl, rp, j', plo, phi, hcs, rfl⟩ | ⟨hcs, -⟩
    · exact Or.inl h0
    · cases hcs; exact Or.inr rfl
    · cases hcs
  subst hD'
  refine ⟨r', ps, hr', hpar.2.1, hpg, hlive, hbr, ?_, ?_, hstep, hpar, hhd, hps, hE, ⟨T, hfr, hT'⟩,
    hDk, hDn, hPd, hfr1⟩
  · rw [hpg, ownSl_congr hfr.2.2.2.2.1, List.flatMap_append, List.flatMap_append, pcUE_D]
    refine slotInv_perm ?_ hsl
    simp only [List.flatMap_append, List.append_assoc]
    refine List.Perm.append_left _ (List.Perm.append_left _ ?_)
    exact List.perm_append_comm.append_left _
  · rw [hpg, List.flatMap_append, List.flatMap_append, pcUE_F, List.append_nil,
      ← List.flatMap_append]
    refine hstep.2.2.2.2.2.2.2.1 _ (fun x hx => ?_) (fun x hx => hfree x ?_)
    · rcases List.mem_append.1 hx with hx | hx
      · exact List.mem_append_left _ (List.mem_append_right _ (ownF_ownSl _ _ x hx))
      · obtain ⟨e, he, hxe⟩ := List.mem_flatMap.1 hx
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 (List.mem_append.1 he |>.elim
          (fun h => List.mem_of_mem_take h) (fun h => List.mem_of_mem_drop h))
        have hkl : k < r.ws.length := by rw [← hb.len]; exact (List.getElem?_eq_some_iff.1 hk).1
        have hD := uEnt_F_D (hb.ent k _ e (List.getElem?_eq_getElem hkl) hk) x hxe
        exact List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, hD⟩)
    · rcases List.mem_append.1 hx with hx | hx
      · exact List.mem_append_left _ hx
      · obtain ⟨e, he, hxe⟩ := List.mem_flatMap.1 hx
        exact List.mem_append_right _ (List.mem_flatMap.2 ⟨e, List.mem_append.1 he |>.elim
          (fun h => List.mem_of_mem_take h) (fun h => List.mem_of_mem_drop h), hxe⟩)

end step

end Spill

end bbolt
end EtcdGrove
end Perennial
