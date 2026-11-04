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

theorem txClean_step {X X' : WX} (h : derefStep X X') (hc : txClean X) : txClean X' := by
  obtain ⟨hv, -, -, -, hrl, htt, hmv, hpm, -, -, -⟩ := id h
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hc
  unfold txClean
  rw [hv, hrl, htt, hmv, hpm, derefStep_bs_isSome h]
  refine ⟨c1, c2, c3, c4, c5, ?_⟩
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
  obtain ⟨C, v, hC, he, hl, hi, hr, hn'⟩ := hn k c hk
  obtain ⟨C', hC', hsC⟩ := derefStep_fwd h hC
  obtain ⟨hbv, hib, -⟩ := bktStep_fields hsC
  refine ⟨C', v, hC', ?_, hl, hi, by rw [hib]; exact hr, by rw [hbv, hib]; exact hn'⟩
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
  obtain ⟨ef, -, ek, ev⟩ := wDat_eq e
  obtain ⟨d1, d2⟩ := he bl B hB l r hr w hw
  rw [← ek, ← ev, ← ef, (nodeStep_nvf hrs).2.1]
  exact ⟨d1, d2⟩

theorem handlesOK_step {X X' : WX} (h : derefStep X X') (hd : objsDisj X.t) (hh : handlesOK X) :
    handlesOK X' := by
  intro b nm hb
  rw [objs_isSome_step h hd]
  rw [h.2.2.1] at hb
  exact hh b nm hb

theorem liveOK_step {X X' : WX} (h : derefStep X X') (hd : objsDisj X.t) (hl : liveOK X) :
    liveOK X' := by
  obtain ⟨l1, l2, l3⟩ := hl
  unfold liveOK
  rw [h.2.1, h.2.2.2.2.1]
  refine ⟨l1, fun l hl => by rw [objs_isSome_step h hd]; exact l2 l hl, ?_⟩
  intro bl B' hB'
  obtain ⟨B, hB, -⟩ := derefStep_bwd h hB'
  exact l3 bl B hB

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
