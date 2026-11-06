/-
`Bucket.spill`'s root loop (U9x, `notes/bbolt-proof-plan.md`): **the spill's global state across
`Cursor.node`'s materializations** (`spG_matGrow`): a materialized node (`nodeAdded`) of a
searchable bucket is clean there (`bktLocalOK`, `BktLoopPurePut.bktLocalOK_nodeAdded_step`), so
`derefPre`'s and `liveFresh`'s node clauses hold of it; it descends from its parent (or is the
bucket's new root node), so `liveReach`; nothing else changes.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopPurePut
public import Proof.go_etcd_io.bbolt.Spill.DerefRel
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSMatT

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section mat
variable [GooseExts]

theorem mem_insert_unit {m : GMap Loc Unit} {a b : Loc} : a ∈ m.insert b () ↔ a = b ∨ a ∈ m := by
  show ((m.insert b ()) !! a).isSome ↔ a = b ∨ (m !! a).isSome
  by_cases h : a = b
  · subst h; rw [GMap.lookup_insert]; simp
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]; simp [h]

theorem dead_none_of_objs' {T : WTx} {l : Loc} (h : T.objs !! l = none) : T.dead !! l = none := by
  have := objs_other T l (Write.objs_none T l h)
  rw [h] at this
  unfold WTx.deadObjs at this
  rw [GMap.lookup_fmap] at this
  cases hd : T.dead !! l with
  | none => rfl
  | some p => rw [hd] at this; cases this

theorem bktReach_bm {X Y : WX} (hrl : Y.rl = X.rl)
    (hbm : ∀ bl B, X.t.bs !! bl = some B → ∃ B', Y.t.bs !! bl = some B' ∧ B'.bm = B.bm)
    {c : Loc} (h : bktReach X c) : bktReach Y c := by
  induction h with
  | root => rw [← hrl]; exact bktReach.root
  | child bl c B n hB hn _ ih =>
    obtain ⟨B', hB', e⟩ := hbm bl B hB
    exact bktReach.child bl c B' n hB' (by rw [e]; exact hn) ih

/-- A chain of parents survives nodes keeping their parents. -/
theorem nodeRootIn_par {B B' : BRec}
    (h : ∀ x rx, B.ns !! x = some rx → ∃ rx', B'.ns !! x = some rx' ∧ rx'.nv.parent' = rx.nv.parent')
    {a rt : Loc} (hr : nodeRootIn B a rt) : nodeRootIn B' a rt := by
  induction hr with
  | top n r hn hp =>
    obtain ⟨r', hr', e⟩ := h n r hn
    exact nodeRootIn.top n r' hr' (by rw [e]; exact hp)
  | up n rt r hn hp _ ih =>
    obtain ⟨r', hr', e⟩ := h n r hn
    refine nodeRootIn.up n rt r' hr' (by rw [e]; exact hp) ?_
    rw [e]; exact ih

/-- **The spill's global state across one materialization** (see the module doc). -/
theorem spG_nodeAdded {X Y : WX} {bl l : Loc} {pgid : w64} {parent : Loc}
    (hadd : nodeAdded X Y bl l pgid parent) (hpos : matPos X bl pgid parent)
    (hlocX : bktLocalOK X bl) (hlocY : bktLocalOK Y bl)
    {txid : w64} {ml : Nat} {fl : FLPg} (hG : spG X txid ml fl) : spG Y txid ml fl := by
  obtain ⟨g1, g2, ⟨dA, dB, dC, dD, dE⟩, gF, ⟨rB, rN⟩, g6, g7, g8, g9⟩ := hG
  obtain ⟨B, pa, pg, r, ns', bv', hB, -, -, hl0, hlo, -, hpar, -, -, -, -, hrcs, -, -, -, -, -,
    -, -, -, hcase, hX'⟩ := hadd
  have hlo' : X.t.objs !! l = none := by simpa using hlo
  have hpos' : (parent = null ∧ B.bv.rootNode' = null ∧ pgid = B.ib.root') ∨
      ∃ i, pagePosAt B parent i pgid := by
    obtain ⟨B', hB', hp⟩ := hpos; rw [hB] at hB'; cases hB'; exact hp
  have hfresh : ∀ c C, X.t.bs !! c = some C → C.ns !! l = none :=
    Write.objs_none X.t l hlo'
  obtain ⟨-, B2, hB2, hcl, hkeys, -, hlv, -⟩ := hlocX
  rw [hB] at hB2; cases hB2
  obtain ⟨hlBY, BY, hBY, hclY, hkY, -, hlvY, -⟩ := hlocY
  subst hX'
  have hBY' : BY = { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' } := by
    have e : (X.t.bs.insert bl { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' }) !! bl =
      some BY := hBY
    rw [GMap.lookup_insert] at e; cases e; rfl
  subst hBY'
  have hbs : ∀ c C, (X.t.bs.insert bl { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' }) !! c
      = some C → (bl = c ∧ C = { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' }) ∨
        (c ≠ bl ∧ X.t.bs !! c = some C) := by
    intro c C hc
    by_cases e : c = bl
    · subst e; rw [GMap.lookup_insert] at hc; cases hc; exact Or.inl ⟨rfl, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hc; exact Or.inr ⟨e, hc⟩
  have hlv1 : ∀ x, x ∈ X.live → x ∈ X.live.insert l () := fun x h => mem_insert_unit.2 (Or.inr h)
  -- the old nodes of `bl`, kept but the parent's children
  have hold : ∀ x rx, B.ns !! x = some rx → ∃ rx', ns' !! x = some rx' ∧
      rx'.nv.parent' = rx.nv.parent' ∧ ∀ c ∈ rx.cs, c ∈ rx'.cs := by
    intro x rx hx
    have hxl : x ≠ l := by intro e; subst e; rw [hfresh bl B hB] at hx; cases hx
    rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', hrp, -, hcs', -, -, -, -, -, hnv, rfl⟩
    · exact ⟨rx, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hxl)]; exact hx, rfl, fun c h => h⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxl)]
      by_cases hxp : x = parent
      · subst hxp; rw [hrp] at hx; cases hx
        refine ⟨rp', GMap.lookup_insert _ _ _, by rw [hnv], fun c h => ?_⟩
        rw [hcs']; exact List.mem_append_left _ h
      · exact ⟨rx, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hxp)]; exact hx, rfl, fun c h => h⟩
  refine ⟨g1, g2, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, g6, g7, g8, g9⟩
  · -- nodes
    intro c C x rx hC hx hxl
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hne, hC'⟩
    · have hnc := hclY.2.2.2.2.2.2.2.1 x rx hx
      refine ⟨hnc.1, hnc.2.2.2.2.1, ?_, fun c' hc' => ?_⟩
      · rcases hnc.2.2.2.2.2.2.2.2.2.2.1 with h | h
        · exact Or.inl h
        · exact Or.inr h.1
      · obtain ⟨rc, hrc, -⟩ := hnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 c' hc'
        exact ⟨hlvY c' rc hrc, by rw [hrc]; rfl⟩
    · have hxl' : x ∈ X.live := by
        rcases mem_insert_unit.1 hxl with e | h
        · subst e; rw [hfresh c C hC'] at hx; cases hx
        · exact h
      obtain ⟨a1, a2, a3, a4⟩ := dA c C x rx hC' hx hxl'
      exact ⟨a1, a2, a3, fun c' hc' => ⟨hlv1 _ (a4 c' hc').1, (a4 c' hc').2⟩⟩
  · -- buckets
    intro c C hC hcl'
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hne, hC'⟩
    · obtain ⟨b1, -⟩ := dB bl B hB hcl'
      refine ⟨fun k c' hk => ?_, fun hrn => ?_⟩
      · obtain ⟨e1, e2⟩ := b1 k c' hk
        refine ⟨e1, ?_⟩
        by_cases e : c' = bl
        · subst e; rw [GMap.lookup_insert]; rfl
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact e2
      · have hnm := hclY.2.2.2.1 hrn
        obtain ⟨-, rt, hrt, -⟩ := hclY.2.2.2.2.1 _ _ hnm
        have hp := hkY.choose_spec.2.1 rt hrt
        exact ⟨_, nodeRootIn.top _ rt hrt hp, hlvY _ rt hrt⟩
    · obtain ⟨b1, b2⟩ := dB c C hC' hcl'
      refine ⟨fun k c' hk => ?_, fun hrn => ?_⟩
      · obtain ⟨e1, e2⟩ := b1 k c' hk
        refine ⟨e1, ?_⟩
        by_cases e : c' = bl
        · subst e; rw [GMap.lookup_insert]; rfl
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact e2
      · obtain ⟨rt, h1, h2⟩ := b2 hrn
        exact ⟨rt, h1, hlv1 _ h2⟩
  · intro c C hC
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hne, hC'⟩
    · refine ⟨hlBY, ?_⟩
      cases h : ns' !! null with
      | none => rfl
      | some rn =>
        exfalso
        have := hclY.2.2.2.2.2.2.2.1 null rn h
        exact hl0 (by
          have hnn := (dC bl B hB).2
          rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', hrp, -, -, -, -, -, -, -, -, rfl⟩
          · by_cases e : null = l
            · exact e.symm
            · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), hnn] at h; cases h
          · by_cases e : null = l
            · exact e.symm
            · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h
              by_cases e2 : null = parent
              · rw [← e2, hnn] at hrp; cases hrp
              · rw [GMap.lookup_insert_ne _ _ (Ne.symm e2), hnn] at h; cases h)
    · exact dC c C hC'
  · show ((X.t.bs.insert bl { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' }) !! X.rl).isSome
    by_cases e : X.rl = bl
    · rw [e, GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact dD
  · intro x hx hxl
    rcases mem_insert_unit.1 hxl with e | h
    · subst e; rw [dead_none_of_objs' hlo'] at hx; cases hx
    · exact dE x hx h
  · -- liveFresh
    intro c C x rx hC hx hxl
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hne, hC'⟩
    · have hnc := hclY.2.2.2.2.2.2.2.1 x rx hx
      refine ⟨hnc.2.2.2.2.2.1, fun hk => ?_⟩
      rcases hnc.2.2.2.2.2.2.2.2.2.2.1 with h | h
      · exact absurd h hk
      · exact h.2
    · have hxl' : x ∈ X.live := by
        rcases mem_insert_unit.1 hxl with e | h
        · subst e; rw [hfresh c C hC'] at hx; cases hx
        · exact h
      exact gF c C x rx hC' hx hxl'
  · -- buckets reached
    intro c C hC hcl'
    have hc0 : ∃ C0, X.t.bs !! c = some C0 := by
      rcases hbs c C hC with ⟨rfl, -⟩ | ⟨-, hC'⟩
      · exact ⟨B, hB⟩
      · exact ⟨C, hC'⟩
    obtain ⟨C0, hC0⟩ := hc0
    refine bktReach_bm (X := X) (by rfl) (fun b Bb hb => ?_) (rB c C0 hC0 hcl')
    by_cases e : b = bl
    · subst e; rw [hB] at hb; cases hb
      exact ⟨_, GMap.lookup_insert _ _ _, rfl⟩
    · exact ⟨Bb, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hb, rfl⟩
  · -- nodes reached
    intro c C x rx hC hx hxl
    rcases hbs c C hC with ⟨rfl, rfl⟩ | ⟨hne, hC'⟩
    · rcases hcase with ⟨hp0, hbv, rfl⟩ | ⟨hp0, hbv, rp, rp', hrp, -, hcs', -, -, -, -, -, hnv, rfl⟩
      · -- the bucket's new root node: no old nodes
        have hrn0 : B.bv.rootNode' = null := by
          rcases hpos' with ⟨-, h, -⟩ | ⟨i, r0, -, hr0, -⟩
          · exact h
          · rw [hp0, (dC bl B hB).2] at hr0; cases hr0
        have hns0 := (hcl.2.2.1 hrn0).1
        have hxl : x = l := by
          by_cases e : x = l
          · exact e
          · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), hns0] at hx; cases hx
        subst hxl
        refine ⟨x, ?_, descIn.self x⟩
        rw [hbv]
        exact nodeRootIn.top x r (GMap.lookup_insert _ _ _) (by rw [hpar, hp0])
      · have hrt : ∀ rt, nodeRootIn B B.bv.rootNode' rt →
            nodeRootIn { B with nm := B.nm.insert pgid l, ns := (B.ns.insert parent rp').insert l r, bv := bv' } bv'.rootNode' rt := by
          intro rt h
          rw [hbv]
          exact nodeRootIn_par (fun y ry hy => by
            obtain ⟨ry', h1, h2, -⟩ := hold y ry hy; exact ⟨ry', h1, h2⟩) h
        have hgrow : ∀ a d, descIn B a d → descIn { B with nm := B.nm.insert pgid l, ns := (B.ns.insert parent rp').insert l r, bv := bv' } a d :=
          descIn_grow B _ (fun y ry hy => by
            obtain ⟨ry', h1, -, h3⟩ := hold y ry hy; exact ⟨ry', h1, h3⟩)
        by_cases e : x = l
        · subst e
          obtain ⟨rt, h1, h2⟩ := rN bl B parent rp hB hrp (hlv parent rp hrp)
          refine ⟨rt, hrt rt h1, descIn_snoc _ rt parent (hgrow rt parent h2) rp' x ?_ ?_⟩
          · have hpl : parent ≠ x := by intro e; rw [e, hfresh bl B hB] at hrp; cases hrp
            show ((B.ns.insert parent rp').insert x r) !! parent = some rp'
            rw [GMap.lookup_insert_ne _ _ (Ne.symm hpl), GMap.lookup_insert]
          · rw [hcs']; exact List.mem_append_right _ (List.mem_singleton_self _)
        · -- an old node
          have hx0 : ∃ rx0, B.ns !! x = some rx0 := by
            rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hx
            by_cases hxp : x = parent
            · exact ⟨rp, by rw [hxp]; exact hrp⟩
            · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxp)] at hx; exact ⟨rx, hx⟩
          obtain ⟨rx0, hrx0⟩ := hx0
          obtain ⟨rt, h1, h2⟩ := rN bl B x rx0 hB hrx0 (hlv x rx0 hrx0)
          exact ⟨rt, hrt rt h1, hgrow rt x h2⟩
    · have hxl' : x ∈ X.live := by
        rcases mem_insert_unit.1 hxl with e | h
        · subst e; rw [hfresh c C hC'] at hx; cases hx
        · exact h
      exact rN c C x rx hC' hx hxl'

/-- **The spill's global state across materializations** of a searchable bucket whose root is a
page (`matGrow_keep`'s premises). -/
theorem spG_matGrow {X X' : WX} {bl : Loc} (h : matGrow X X' bl) (hbl : bktLocalOK X bl)
    (h0 : ∀ B, X.t.bs !! bl = some B → B.ib.root' ≠ W64 0)
    {txid : w64} {ml : Nat} {fl : FLPg} (hG : spG X txid ml fl) : spG X' txid ml fl := by
  induction h with
  | refl => exact hG
  | step X Y Z bl l pgid parent hadd hpos hm ih =>
    have hbl' := bktLocalOK_nodeAdded_step hbl hadd hpos
    have h0' : ∀ B, Y.t.bs !! bl = some B → B.ib.root' ≠ W64 0 := by
      obtain ⟨-, -, -, hib, -⟩ := matGrow_keep (matGrow.step X Y Y bl l pgid parent hadd hpos
        (matGrow.refl Y bl)) hbl h0
      obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 (show (X.t.bs !! bl).isSome by
        obtain ⟨-, B, hB, -⟩ := hbl; rw [hB]; rfl)
      obtain ⟨B', hB', e⟩ := hib B hB
      intro B'' hB''; rw [hB'] at hB''; cases hB''; rw [e]; exact h0 B hB
    exact ih hbl' h0' (spG_nodeAdded hadd hpos hbl hbl' hG)

end mat

end Spill

end bbolt
end EtcdGrove
end Perennial
