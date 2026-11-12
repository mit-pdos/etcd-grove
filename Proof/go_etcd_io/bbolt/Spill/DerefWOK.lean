/-
`derefStep` keeps `wOK` (U9b, `notes/bbolt-proof-plan.md`; pure): from the node and bucket
parts (`DerefWOK1`), the transaction's clean invariant, keys, nested buckets, nodes' pages,
bounded entries, handles, live set and node registry.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.DerefWOK1

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wok
variable [GooseExts]

theorem derefStep_bs_isSome {X X' : WX} (h : derefStep X X') (bl : Loc) :
    (X'.t.bs !! bl).isSome = (X.t.bs !! bl).isSome :=
  optRel_isSome (derefStep_bs h bl)

theorem derefStep_bwd {X X' : WX} (h : derefStep X X') {bl : Loc} {B' : BRec}
    (hB : X'.t.bs !! bl = some B') : ∃ B, X.t.bs !! bl = some B ∧ bktStep B B' :=
  optRel_some_r (hB ▸ derefStep_bs h bl)

theorem derefStep_fwd {X X' : WX} (h : derefStep X X') {bl : Loc} {B : BRec}
    (hB : X.t.bs !! bl = some B) : ∃ B', X'.t.bs !! bl = some B' ∧ bktStep B B' :=
  optRel_some_l (hB ▸ derefStep_bs h bl)

/-- Dereferencing keeps the leaves' root shape (batch 30): the entries' flags and the nodes'
`isLeaf` are kept. -/
theorem leafShape_step {X X' : WX} (h : derefStep X X') (hs : leafShape X) : leafShape X' := by
  intro bl B' hB' l r' hr' hleaf w hw
  obtain ⟨B, hB, hst⟩ := derefStep_bwd h hB'
  rw [h.2.2.2.2.1]
  obtain ⟨r, hr, hns⟩ := optRel_some_r (hr' ▸ hst.2 l)
  rcases hns with rfl | hd
  · exact hs bl B hB l r' hr hleaf w hw
  · have hl : r.nv.isLeaf' = true := by rw [← hleaf, hd.1]
    have hm : wDat w ∈ r.ws.map wDat := by rw [← hd.2.2.1]; exact List.mem_map_of_mem hw
    obtain ⟨w0, hw0, he⟩ := List.mem_map.1 hm
    have hf : w0.flags = w.flags := congrArg Prod.fst he
    rw [← hf]
    exact hs bl B hB l r hr hl w0 hw0

/-- A page position of a dereferenced bucket is one of the bucket's before (batch 35): the
header, the root node and the node cache are kept, a node's `isLeaf` and its entries' page ids
too. -/
theorem posRoot_bktStep {B B' : BRec} (hst : bktStep B B') {c : Nat} (h : posRoot B' c) :
    posRoot B c := by
  have e := hst.1
  have hbv : B'.bv = B.bv := by rw [← e]
  have hib : B'.ib = B.ib := by rw [← e]
  have hnm : B'.nm = B.nm := by rw [← e]
  rcases h with ⟨h1, h2, h3⟩ | ⟨l, i, ⟨r', w, hr', hlf, hw, hpg, hnm'⟩, hc⟩
  · exact Or.inl ⟨hbv ▸ h1, hib ▸ h2, hib ▸ h3⟩
  · right
    obtain ⟨r, hr, hns⟩ := optRel_some_r (hr' ▸ hst.2 l)
    rcases hns with rfl | hd
    · exact ⟨l, i, ⟨r', w, hr, hlf, hw, hpg, hnm ▸ hnm'⟩, hc⟩
    · have hl : r.nv.isLeaf' = false := by rw [← hlf, hd.1]
      have hm := congrArg (fun L => L[i]?) hd.2.2.1
      simp only [List.getElem?_map, hw, Option.map_some] at hm
      cases hri : r.ws[i]? with
      | none => rw [hri] at hm; cases hm
      | some w0 =>
        rw [hri] at hm
        have : w0.pgid = w.pgid := congrArg (fun x => x.2.1) (Option.some.inj hm).symm
        exact ⟨l, i, ⟨r, w0, hr, hl, hri, this.trans hpg, hnm ▸ hnm'⟩, hc⟩

/-- Dereferencing keeps the view pages' root shape under the page positions (batch 35). -/
theorem posShape_step {X X' : WX} (h : derefStep X X') (hs : posShape X) : posShape X' := by
  intro bl B' hB' c p pg hc hp hpg hl i hi
  obtain ⟨B, hB, hst⟩ := derefStep_bwd h hB'
  rw [h.1] at hp hpg
  rw [h.2.2.2.2.1, h.1]
  exact hs bl B hB c p pg (posRoot_bktStep hst hc) hp hpg hl i hi

/-- Dereferencing keeps the root bucket not inline (batch 37: its header is kept). -/
theorem rootNotInline_step {X X' : WX} (h : derefStep X X') (hr : rootNotInline X) :
    rootNotInline X' := by
  intro B' hB'
  obtain ⟨hv, -, -, -, hrl, -⟩ := id h
  rw [hrl] at hB'
  obtain ⟨B, hB, hst⟩ := derefStep_bwd h hB'
  rw [(bktStep_fields hst).2.1]
  exact hr B hB

theorem txClean_step {X X' : WX} (h : derefStep X X') (hc : txClean X) : txClean X' := by
  have hrni := fun hr => rootNotInline_step h hr
  obtain ⟨hv, -, -, -, hrl, htt, hmv, hpm, hbuf, -, -, -⟩ := id h
  obtain ⟨c1, ⟨c2, c2b, c2s, c2p, c2r⟩, c3, c4, c5, c6⟩ := hc
  have c2s' := leafShape_step h c2s
  have c2p' := posShape_step h c2p
  have c2r' := hrni c2r
  unfold txClean
  rw [hv, hrl, htt, hmv, hpm, hbuf, derefStep_bs_isSome h]
  refine ⟨c1, ⟨c2, c2b, c2s', c2p', c2r'⟩, c3, c4, c5, ?_⟩
  intro bl B' hB'
  obtain ⟨B, hB, hs⟩ := derefStep_bwd h hB'
  obtain ⟨d1, d2⟩ := c6 bl B hB
  refine ⟨bktClean_step hs d1, ?_⟩
  intro name c hc
  rw [derefStep_bs_isSome h]
  exact d2 name c (by rw [← (bktStep_fields hs).2.2.2.1]; exact hc)

theorem bktNested_step {X X' : WX} (h : derefStep X X') {B B' : BRec} (hs : bktStep B B')
    (hn : bktNested X.v X.t B) : bktNested X'.v X'.t B' := by
  intro k c hk
  rw [(bktStep_fields hs).2.2.2.1] at hk
  obtain ⟨C, v, hC, he, hl, hi, hr, hn', hp, hbo, htk⟩ := hn k c hk
  obtain ⟨C', hC', hsC⟩ := derefStep_fwd h hC
  obtain ⟨hbv, hib, -, -, hipg, -⟩ := bktStep_fields hsC
  refine ⟨C', v, hC', ?_, hl, hi, by rw [hib]; exact hr, by rw [hbv, hib]; exact hn',
    by rw [hbv, hib, hipg]; exact hp, by rw [h.1, h.2.2.2.2.2.2.1]; exact hbo,
    by rw [h.1]; exact htk⟩
  rw [h.1]; exact entryIn_step hs he

theorem txPg_step {X X' : WX} (h : derefStep X X') (hp : txPg X.v X.t.bs) : txPg X'.v X'.t.bs := by
  intro bl B' hB' l r' hr'
  obtain ⟨B, hB, hs⟩ := derefStep_bwd h hB'
  obtain ⟨r, hr, hrs⟩ := bktStep_bwd hs hr'
  rw [h.1, (bktStep_fields hs).2.1]
  exact nodePg_step hrs (hp bl B hB l r hr)

theorem entriesBounded_step {X X' : WX} (h : derefStep X X') (he : entriesBounded X) :
    entriesBounded X' := by
  intro bl B' hB' l r' hr' w' hw'
  obtain ⟨B, hB, hs⟩ := derefStep_bwd h hB'
  obtain ⟨r, hr, hrs⟩ := bktStep_bwd hs hr'
  obtain ⟨w, hw, e, -⟩ := nodeStep_mem hrs hw'
  obtain ⟨-, -, ek, ev⟩ := wDat_eq e
  have d := he bl B hB l r hr w hw
  rw [← ek, ← ev, h.2.2.2.2.1]
  exact d

theorem handlesOK_step {X X' : WX} (h : derefStep X X') (hd : objsDisj X.t) (hh : handlesOK X) :
    handlesOK X' := by
  intro b nm hb
  rw [h.2.2.1] at hb
  have e : (X'.t.bobjs !! b).isSome = (X.t.bobjs !! b).isSome := by
    simp only [WTx.bobjs, GMap.lookup_union, h.2.2.2.2.2.2.2.2.2.2.1]
    have := derefStep_bs_isSome h b
    revert this
    cases X.t.bs !! b <;> cases X'.t.bs !! b <;> simp
  rw [e]
  exact hh b nm hb

theorem liveOK_step {X X' : WX} (h : derefStep X X') (hd : objsDisj X.t) (hl : liveOK X) :
    liveOK X' := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := hl
  unfold liveOK
  rw [h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1]
  refine ⟨l1, fun l hl => by rw [objs_isSome_step h hd]; exact l2 l hl, ?_, ?_, ?_⟩
  · intro bl B' hB'
    obtain ⟨B, hB, -⟩ := derefStep_bwd h hB'
    exact l3 bl B hB
  · intro bl B' l r' hB' hr'
    obtain ⟨B, hB, hs⟩ := optRel_some_r (hB' ▸ derefStep_bs h bl)
    obtain ⟨r, hr, -⟩ := optRel_some_r (hr' ▸ hs.2 l)
    rw [h.2.1]; exact l4 bl B l r hB hr
  · intro l hl
    rw [h.2.2.2.2.2.2.2.2.2.1] at hl
    exact l5 l hl

theorem nlocOK_step {X X' : WX} (h : derefStep X X') (hn : nlocOK X) : nlocOK X' := by
  intro n b p hnl hl
  rw [h.2.2.2.1] at hnl
  rw [h.2.1] at hl
  obtain ⟨B, r, hB, hr, hp⟩ := hn n b p hnl hl
  obtain ⟨B', hB', hs⟩ := derefStep_fwd h hB
  obtain ⟨r', hr', hrs⟩ := bktStep_fwd hs hr
  exact ⟨B', r', hB', hr', by rw [(nodeStep_nvf hrs).2.2.2.2.1]; exact hp⟩

/-- **A `derefStep` keeps `wOK`** (the objects disjoint). -/
theorem wOK_derefStep (X X' : WX) (h : derefStep X X') (hd : objsDisj X.t) (hok : wOK X) :
    wOK X' := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := hok
  refine ⟨txClean_step h o1, ?_, txPg_step h o3, entriesBounded_step h o4, handlesOK_step h hd o5,
    liveOK_step h hd o6, nlocOK_step h o7, by rw [h.1]; exact o8⟩
  intro bl B' hB'
  obtain ⟨B, hB, hs⟩ := derefStep_bwd h hB'
  obtain ⟨k1, k2⟩ := o2 bl B hB
  exact ⟨by rw [h.1]; exact bktKeys_step hs k1, bktNested_step h hs k2⟩

end wok

end bbolt
end EtcdGrove
end Perennial
