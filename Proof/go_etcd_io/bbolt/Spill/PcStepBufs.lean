/-
`node.spill` after its children's loop (U9z3, `notes/bbolt-proof-plan.md`; pure): **a piece's
step keeps the buffers dirty pages of fresh slots** (`pcStepX_bufsOK`, `spStep`'s `bufsOK`
clause), from the writer's facts `spPre` carries (the view the committed tree's, the free ids
covering no tree slot, the tree's slots below the mark); and **a piece's step is a spill step**
(`pcStepX_step`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailStepState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section bufs
variable [GooseExts] [GoGlobalContext]

theorem wsMs_congr' {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat) :
    wsMs ws' = wsMs ws := by
  have e : ∀ l : List WEntry, wsMs l =
      (l.map wDat).map (fun d => (⟨d.1, d.2.1, d.2.2.1, d.2.2.2⟩ : InodeM)) := by
    intro l; unfold wsMs; rw [List.map_map]; rfl
  rw [e, e, h]

/-- **The pending slots after a piece's step**: the ones before, or tree slots (the piece's freed
page's, a page of the committed tree). -/
theorem pcStep_pendSub {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} (hs : pcStep Xi wi bl l rl count X3 w2 st id)
    (hv : Xi.v.pages = wi.C.pages)
    (htl : ∀ s ∈ treeSlots wi.C, s < Xi.t.mv.pgid'.toNat)
    (hm62 : Xi.t.mv.pgid'.toNat < 2 ^ 62) :
    ∀ s ∈ pendSlots w2.fl, s ∈ pendSlots wi.fl ∨ s ∈ treeSlots wi.C := by
  obtain ⟨X1, w1, X2, p, ra, rp, s, ins, stf, sta, hfr, -, hal, -, -, -, -, -, -, -, -⟩ := hs
  have hp2 := (allocRes_fl hal).1
  intro y hy
  rw [hp2] at hy
  rcases hfr with ⟨-, -, rfl, -⟩ | ⟨pg, -, hpg, -, rfl, -⟩
  · exact Or.inl hy
  · have hcov : ∀ t, rl.nv.pgid'.toNat ≤ t → t < rl.nv.pgid'.toNat + (1 + pageOverflow pg) →
        t ∈ treeSlots wi.C := by
      intro t h1 h2
      unfold treeSlots
      rw [mem_pagesSlots_iff]
      exact ⟨_, pg, by rw [← hv]; exact hpg, h1, h2⟩
    have hlt := htl _ (hcov (rl.nv.pgid'.toNat + pageOverflow pg) (by omega) (by omega))
    rcases (pendSlots_freePages wi.fl wi.wtxid rl.nv.pgid' (1 + pageOverflow pg) (by omega) y).1
      hy with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (hcov y h1 h2)

/-- **A piece's step keeps the buffers dirty pages of fresh slots** (`spStep`'s `bufsOK`
clause): the new buffer's header and length `node.write`'s, its id at least `2` (a free id's or
the mark's), its run below the new mark and on no tree slot (a free id covers none, the mark is
above them) and on no pending slot (a free id is not pending, the pending ids are below the mark;
the freed page's slots are tree slots). -/
theorem pcStepX_bufsOK {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} (hs : pcStep Xi wi bl l rl count X3 w2 st id)
    (hn : Xi.node bl l = some rl) (hpl : rl.nv.parent' ≠ null → rl.nv.parent' ≠ l)
    (hG1 : ∀ X1 w1 st, pcFreed Xi wi bl l rl X1 w1 st → spG X1 wi.wtxid (mapLen w1.ms) w1.fl)
    (hcnt : count - 1 < 2 ^ 32)
    (hbody : 16 + (pageBody true (wsMs rl.ws)).length ≤ count * 4096)
    (hv : Xi.v.pages = wi.C.pages)
    (hfc : ∀ y ∈ wi.fl.free, ¬ coversSlot wi.C.pages y.toNat)
    (htl : ∀ s ∈ treeSlots wi.C, s < Xi.t.mv.pgid'.toNat)
    (hnd : wi.fl.allIds.Nodup) (hal : ∀ y ∈ wi.fl.allIds, y.toNat < Xi.t.mv.pgid'.toNat) :
    bufsOK Xi wi.C wi.fl → bufsOK X3 wi.C w2.fl := by
  intro hB
  obtain ⟨ra, -, -, -, q, -, hsa, -, -, -, -, hmk3, hext3, hc0, hbuf3, -⟩ :=
    pcStepX_state hs hn hpl hG1 (fun y hy => hal y (List.mem_append_left _ hy))
  have hfr0 := hs
  obtain ⟨X1, w1, X2, p, ra', rp, s, ins, stf, sta, hfr, -, hAl, -, -, -, -, -, -, -, -⟩ := hfr0
  have hG := hG1 X1 w1 stf hfr
  obtain ⟨hmv, -, -, -, -, -, -, hfree, -⟩ := pcFreed_basic hfr
  have hm62 : Xi.t.mv.pgid'.toNat < 2 ^ 62 := by rw [← hmv]; exact hG.2.2.2.2.2.2.1
  have hpend := pcStep_pendSub hs hv htl hm62
  have hp2 := (allocRes_fl hAl).1
  have hms : wsMs ra.ws = wsMs rl.ws := wsMs_congr' hsa.2.2.1
  intro y pg hy
  rw [hbuf3] at hy
  by_cases hyid : y = id
  · subst hyid
    rw [GMap.lookup_insert_eq] at hy
    cases hy
    have hov : pageOverflow (pcPage y ra.nv.isLeaf' ra.ws count) = count - 1 := by
      unfold pcPage; rw [wPage_overflow]; word
    rw [hov]
    refine ⟨by unfold pcPage; rw [wPage_id], ?_, ?_, by omega, ?_⟩
    · unfold pcPage
      rw [wPage_length, List.length_replicate, hms]
      simp only [pageBody_length] at hbody ⊢
      omega
    · rcases (allocRes_basic hAl).2.2.2.2 with ⟨hcan, -, -⟩ | ⟨hid, -, -, -⟩
      · exact hG.2.2.2.2.2.2.2.2.2.2 y (hcan.2 y (by unfold inRun; omega))
      · rw [hid]; exact hG.2.2.2.2.2.2.2.2.2.1
    · intro j hj
      rcases (allocRes_basic hAl).2.2.2.2 with ⟨hcan, -, -⟩ | ⟨hid, -, hlt, -⟩
      · have ht : (y + W64 (j : Int)).toNat = y.toNat + j := by have := hcan.1; word
        have hin : y + W64 (j : Int) ∈ wi.fl.free := by
          rw [← hfree]; exact hcan.2 _ (by unfold inRun; omega)
        have hnt : y.toNat + j ∉ treeSlots wi.C := by
          intro hm; unfold treeSlots at hm; rw [mem_pagesSlots_iff] at hm
          exact hfc _ hin (by rw [ht]; exact hm)
        refine ⟨hnt, fun hm => ?_⟩
        rcases hpend _ hm with hm | hm
        · obtain ⟨z, hz, hze⟩ := List.mem_map.1 hm
          have hzi : z = y + W64 (j : Int) := BitVec.eq_of_toNat_eq (by rw [hze, ht])
          rw [hzi] at hz
          exact (List.nodup_append.1 hnd).2.2 _ hin _ hz rfl
        · exact hnt hm
      · have hy0 : y.toNat = Xi.t.mv.pgid'.toNat := by rw [hid, hmv]
        have hnt : y.toNat + j ∉ treeSlots wi.C := fun hm => by have := htl _ hm; omega
        refine ⟨hnt, fun hm => ?_⟩
        rcases hpend _ hm with hm | hm
        · obtain ⟨z, hz, hze⟩ := List.mem_map.1 hm
          have := hal z (List.mem_append_right _ hz)
          omega
        · exact hnt hm
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hyid)] at hy
    obtain ⟨h1, h2, h3, h4, h5⟩ := hB y pg hy
    refine ⟨h1, h2, h3, by omega, fun j hj => ⟨(h5 j hj).1, fun hm => ?_⟩⟩
    rcases hpend _ hm with hm | hm
    · exact (h5 j hj).2 hm
    · exact (h5 j hj).1 hm

/-- **A piece's step is a spill step** for the slots `O` (owned with `L`, which holds the piece's
own page, if any). -/
theorem pcStepX_step {Xi X3 : WX} {wi w2 : WDb} {bl l : Loc} {rl : NRec} {count : Nat}
    {st : List FLStep} {id : w64} {O L : List Nat} (hs : pcStep Xi wi bl l rl count X3 w2 st id)
    (hn : Xi.node bl l = some rl)
    (hG3 : spG X3 wi.wtxid (mapLen w2.ms) w2.fl)
    (hsl : slotInv wi.fl Xi.t.mv.pgid'.toNat (O ++ L))
    (hown : rl.nv.pgid' ≠ W64 0 → rl.nv.pgid'.toNat ∈ L)
    (hpl : rl.nv.parent' ≠ null → rl.nv.parent' ≠ l)
    (hG1 : ∀ X1 w1 st, pcFreed Xi wi bl l rl X1 w1 st → spG X1 wi.wtxid (mapLen w1.ms) w1.fl)
    (hcnt : count - 1 < 2 ^ 32)
    (hbody : 16 + (pageBody true (wsMs rl.ws)).length ≤ count * 4096)
    (hv : Xi.v.pages = wi.C.pages)
    (hfc : ∀ y ∈ wi.fl.free, ¬ coversSlot wi.C.pages y.toNat)
    (htl : ∀ s ∈ treeSlots wi.C, s < Xi.t.mv.pgid'.toNat) :
    spStep Xi X3 wi w2 O st := by
  have hbk := pcStepX_bufsOK hs hn hpl hG1 hcnt hbody hv hfc htl hsl.2.2.1 hsl.2.2.2
  have hfresh := pcStepX_fresh hs hsl
  obtain ⟨X1, w1, X2, p, ra, rp, s, ins, stf, sta, hfr, rfl, hal, hfl2, -, hC, -, -, -, -, hX3⟩ := hs
  obtain ⟨hmv, hbf, hpm1, hv1, -, hC1, -, hfree, hfl1⟩ := pcFreed_basic hfr
  obtain ⟨hpd1, hal1⟩ := pcFreed_fl hfr
  obtain ⟨hpd2, hal2⟩ := allocRes_fl hal
  obtain ⟨hab1, -, -, hab4, hab5⟩ := allocRes_basic hal
  have hpm2 := allocRes_pm hal
  have hc0 : 0 < count := hal.1
  have hbf3 : X3.t.bufs = X2.t.bufs.insert id (pcPage id ra.nv.isLeaf' ra.ws count) := by
    rw [hX3]; unfold pcFin WX.setBuf; split <;> simp only [setNode_t_bufs]
  have hpm3 : X3.t.pm = X2.t.pm := by
    rw [hX3]; unfold pcFin WX.setBuf; split <;> simp only [setNode_t_pm]
  have hv3 : X3.v = X2.v := by
    rw [hX3]; unfold pcFin WX.setBuf; split <;> simp only [WX.setNode_v]
  have hb : X3.t.bufs = Xi.t.bufs.insert id (pcPage id ra.nv.isLeaf' ra.ws count) := by
    rw [hbf3, hab4, hbf, GMap.insert_insert]
  have hvp : X3.v.pages = Xi.v.pages := by rw [hv3, hab1, hv1]
  obtain ⟨-, hPne⟩ := spP_bufs_insert hb hvp
  have hidO : ∀ y ∈ O, y ≠ id.toNat := fun y hy he => by
    rcases hfresh y (List.mem_append_left _ hy) with h | h <;> omega
  have hidP : id.toNat ∉ pendSlots wi.fl := by
    intro hm
    obtain ⟨z, hz, hze⟩ := List.mem_map.1 hm
    have hzi : z = id := BitVec.eq_of_toNat_eq hze
    rw [hzi] at hz
    rcases hab5 with ⟨hcan, -, -⟩ | ⟨hid, -, -, -⟩
    · have hin : id ∈ w1.fl.free := hcan.2 id (by unfold inRun; omega)
      rw [hfree] at hin
      exact (List.nodup_append.1 hsl.2.2.1).2.2 id hin id hz rfl
    · have := hsl.2.2.2 id (List.mem_append_right _ hz)
      rw [hid, hmv] at this; omega
  refine ⟨by rw [hC, hC1], by rw [applySteps_append, hfl2, hfl1], hvp, hG3, hG3.2.1, ?_, ?_, ?_, ?_⟩
  · intro y hy; rw [hpd2]; exact hpd1 y hy
  · intro x hx
    have hxe : x = id.toNat := Classical.byContradiction fun hne => hx (hPne x hne)
    subst hxe; exact ⟨fun hm => hidO _ hm rfl, hidP⟩
  · intro F hFO hF y hy
    obtain ⟨h1, h2⟩ := hF y hy
    have hyO := hFO y hy
    have hy62 := (hsl.2.1 y (List.mem_append_left _ hyO)).2.1
    have hyid : id ≠ W64 (y : Int) := by
      intro he; apply hidO y hyO; rw [he, w64_toNat_of_lt hy62]
    refine ⟨?_, ?_⟩
    · rw [hpm3, hpm2, GMap.lookup_insert_ne _ _ hyid, hpm1]; exact h1
    · rw [hal2 _ (Ne.symm hyid), hal1]
      · exact h2
      · rintro ⟨he, hp0⟩
        have hL := hown hp0
        rw [← he, w64_toNat_of_lt hy62] at hL
        exact (List.nodup_append.1 hsl.1).2.2 y hyO y hL rfl
  · exact hbk

end bufs

end Spill

end bbolt
end EtcdGrove
end Perennial
