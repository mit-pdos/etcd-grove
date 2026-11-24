/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureT/Coord.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A2 (totality): the coordinator's records (`CoordOK`) under the coordinator's updates.
-/
module

public import Dsverify.Proof.gryff.PureT.StepPart

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.tot

open model kahn

theorem msb_of_toInt {b : w32} (h : 0 ≤ b.toInt) : b.msb = false := by
  rw [BitVec.toInt_eq_msb_cond] at h
  cases hm : b.msb
  · rfl
  · rw [hm] at h; simp at h; have := b.isLt; omega

theorem shiftInts_low (a b : w32) : (shiftInts a b).setWidth 32 = b := by
  ext i hi
  simp [shiftInts, BitVec.getElem_setWidth, BitVec.getLsbD_signExtend, hi]
  intro; omega

theorem shiftInts_high (a b : w32) (hb : b.msb = false) : (shiftInts a b).extractLsb' 32 32 = a := by
  ext i hi
  simp [shiftInts, BitVec.getLsbD_signExtend, hi, hb]
  have h1 : 32 + i < 64 := by omega
  have h2 : ¬ (32 + i < 32) := by omega
  have h3 : i < 64 := by omega
  simp [h1, h2, h3]

theorem shiftInts_inj {a b a' b' : w32} (hb : 0 ≤ b.toInt) (hb' : 0 ≤ b'.toInt)
    (h : shiftInts a b = shiftInts a' b') : a = a' ∧ b = b' := by
  have hb1 := msb_of_toInt hb
  have hb2 := msb_of_toInt hb'
  constructor
  · rw [← shiftInts_high a b hb1, ← shiftInts_high a' b' hb2, h]
  · rw [← shiftInts_low a b, ← shiftInts_low a' b', h]

section
variable {mx : w32} {oq : AMap 32 OngoingOp} {ws : AMap 64 WriteOp} {rs : AMap 64 ReadOp}
  {u : List (w32 × w32)}

theorem CoordOK.mono_used (h : CoordOK mx oq ws rs u) {u' : List (w32 × w32)}
    (hu : ∀ p ∈ u, p ∈ u') : CoordOK mx oq ws rs u' where
  oreq := h.oreq
  wops := fun e he => by
    obtain ⟨a, b, c, d, f, g⟩ := h.wops e he; exact ⟨a, b, c, d, f, hu _ g⟩
  wopsN := h.wopsN
  rops := h.rops

/-- A read completes (`rops` and its `OngoingReqs` entry deleted). -/
theorem CoordOK.delRead (h : CoordOK mx oq ws rs u) {id : w64} {rop : ReadOp}
    (hr : rs.get? id = some rop) : CoordOK mx (oq.del rop.n) ws (rs.del id) u where
  oreq := by
    intro k o hk
    rw [AMap.get?_del] at hk; split at hk; · cases hk
    obtain ⟨a, b⟩ := h.oreq k o hk
    refine ⟨a, fun k' hk' => ⟨(b k' hk').1, fun o' ho' => ?_⟩⟩
    rw [AMap.get?_del] at ho'; split at ho'; · cases ho'
    exact (b k' hk').2 o' ho'
  wops := by
    intro e he
    obtain ⟨a, ⟨o, ho, hro⟩, c⟩ := h.wops e he
    refine ⟨a, ⟨o, ?_, hro⟩, c⟩
    rw [AMap.get?_del]; split
    · next heq =>
      have := (h.rops id rop hr).2.2 o (heq ▸ ho); rw [this] at hro; cases hro
    · exact ho
  wopsN := h.wopsN
  rops := by
    intro id' rop' hr'
    rw [AMap.get?_del] at hr'; split at hr'; · cases hr'
    obtain ⟨a, b, c⟩ := h.rops id' rop' hr'
    refine ⟨a, b, fun o ho => ?_⟩
    rw [AMap.get?_del] at ho; split at ho; · cases ho
    exact c o ho

/-- A write completes (`wops` and its `OngoingReqs` entry deleted). -/
theorem CoordOK.delWrite (h : CoordOK mx oq ws rs u) {id : w64} {w : WriteOp}
    (hw : ws.get? id = some w) : CoordOK mx (oq.del w.n) (ws.del id) rs u where
  oreq := by
    intro k o hk
    rw [AMap.get?_del] at hk; split at hk; · cases hk
    obtain ⟨a, b⟩ := h.oreq k o hk
    refine ⟨a, fun k' hk' => ⟨(b k' hk').1, fun o' ho' => ?_⟩⟩
    rw [AMap.get?_del] at ho'; split at ho'; · cases ho'
    exact (b k' hk').2 o' ho'
  wops := by
    intro e he
    obtain ⟨he1, he2⟩ := AMap.mem_del he
    obtain ⟨a, ⟨o, ho, hro⟩, c⟩ := h.wops e he1
    refine ⟨a, ⟨o, ?_, hro⟩, c⟩
    rw [AMap.get?_del]; split
    · next heq => exact absurd (h.wopsN e he1 (id, w) (AMap.mem_of_get? hw) heq) he2
    · exact ho
  wopsN := fun e1 h1 e2 h2 => h.wopsN e1 (AMap.mem_del h1).1 e2 (AMap.mem_del h2).1
  rops := by
    intro id' rop' hr'
    obtain ⟨a, b, c⟩ := h.rops id' rop' hr'
    refine ⟨a, b, fun o ho => ?_⟩
    rw [AMap.get?_del] at ho; split at ho; · cases ho
    exact c o ho

/-- A write record is updated (same `N`, key fields; the shapes kept). -/
theorem CoordOK.updWrite (h : CoordOK mx oq ws rs u) {id : w64} {w w' : WriteOp}
    (hw : ws.get? id = some w) (hn : w'.n = w.n) (hv : w'.maxValTag.v = -1)
    (ha : w'.numWrite1Applies = 0) (hr : w'.requestId = w.requestId)
    (hc : w'.clientId = w.clientId) : CoordOK mx oq (ws.put id w') rs u where
  oreq := h.oreq
  wops := by
    intro e he
    rcases AMap.mem_put he with rfl | he
    · obtain ⟨a, b, _, _, f, g⟩ := h.wops (id, w) (AMap.mem_of_get? hw)
      exact ⟨by rw [hn]; exact a, by rw [hn]; exact b, hv, ha, by rw [hr, hc]; exact f,
        by rw [hr, hc]; exact g⟩
    · exact h.wops e he
  wopsN := by
    have hm := AMap.mem_of_get? hw
    intro e1 h1 e2 h2 heq
    rcases AMap.mem_put h1 with rfl | h1 <;> rcases AMap.mem_put h2 with rfl | h2
    · rfl
    · exact h.wopsN (id, w) hm e2 h2 (by rw [← heq]; exact hn.symm)
    · exact h.wopsN e1 h1 (id, w) hm (by rw [heq]; exact hn)
    · exact h.wopsN e1 h1 e2 h2 heq
  rops := h.rops

/-- A new write (`N = maxN + 1`, a fresh key). -/
theorem CoordOK.newWrite (h : CoordOK mx oq ws rs u) (hmx : mx.toNat < 24) (rid cid : w32)
    (w : WriteOp) (hn : w.n = mx + 1) (hv : w.maxValTag.v = -1) (ha : w.numWrite1Applies = 0)
    (hr : w.requestId = rid) (hc : w.clientId = cid) :
    CoordOK (mx + 1) (oq.put (mx + 1) ⟨rid, cid, false, []⟩) (ws.put (shiftInts rid cid) w) rs
      ((cid, rid) :: u) := by
  have hN : (mx + 1).toNat = mx.toNat + 1 := by
    rw [BitVec.toNat_add]; simp; omega
  have hne : ∀ k : w32, k.toNat ≤ mx.toNat → k ≠ mx + 1 := by
    intro k hk he; rw [he, hN] at hk; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k o hk
    rw [AMap.get?_put] at hk
    split at hk
    · next heq => cases hk; subst heq; exact ⟨Nat.le_refl _, by simp⟩
    · obtain ⟨a, b⟩ := h.oreq k o hk
      refine ⟨by omega, fun k' hk' => ⟨by have := (b k' hk').1; omega, fun o' ho' => ?_⟩⟩
      rw [AMap.get?_put] at ho'
      split at ho'
      · next heq => exact absurd heq (hne k' (b k' hk').1)
      · exact (b k' hk').2 o' ho'
  · intro e he
    rcases AMap.mem_put he with rfl | he
    · refine ⟨by rw [hn]; exact Nat.le_refl _, ⟨⟨rid, cid, false, []⟩, by rw [hn, AMap.get?_put]; simp,
        rfl⟩, hv, ha, by rw [hr, hc],
        by simp [hr, hc]⟩
    · obtain ⟨a, ⟨o, ho, hro⟩, c, d, f, g⟩ := h.wops e he
      refine ⟨by omega, ⟨o, ?_, hro⟩, c, d, f, by simp [g]⟩
      rw [AMap.get?_put, if_neg (hne _ a)]; exact ho
  · intro e1 h1 e2 h2 heq
    rcases AMap.mem_put h1 with rfl | h1 <;> rcases AMap.mem_put h2 with rfl | h2
    · rfl
    · exact absurd (heq ▸ hn) (hne _ (h.wops e2 h2).1)
    · exact absurd (heq.symm ▸ hn) (hne _ (h.wops e1 h1).1)
    · exact h.wopsN e1 h1 e2 h2 heq
  · intro id rop hr'
    obtain ⟨a, b, c⟩ := h.rops id rop hr'
    refine ⟨a, by omega, fun o ho => ?_⟩
    rw [AMap.get?_put, if_neg (hne _ b)] at ho; exact c o ho

/-- The `OngoingReqs` after a new read's loop over the writes: the same keys and kinds, each
entry's `ShortReads` extended by the read's `n` only. -/
def OqExt (n : w32) (oq1 oq2 : AMap 32 OngoingOp) : Prop :=
  ∀ k, (oq2.get? k).isSome = (oq1.get? k).isSome ∧ ∀ o2, oq2.get? k = some o2 →
    ∃ o1, oq1.get? k = some o1 ∧ o2.isRead = o1.isRead ∧ ∀ x ∈ o2.shortReads, x ∈ o1.shortReads ∨ x = n

theorem OqExt.refl (n : w32) (oq : AMap 32 OngoingOp) : OqExt n oq oq :=
  fun _ => ⟨rfl, fun o2 h => ⟨o2, h, rfl, fun x hx => Or.inl hx⟩⟩

theorem OqExt.put {n : w32} {oq1 oq2 : AMap 32 OngoingOp} (h : OqExt n oq1 oq2) {k : w32}
    {op : OngoingOp} (hk : oq2.get? k = some op) :
    OqExt n oq1 (oq2.put k { op with shortReads := op.shortReads ++ [n] }) := by
  intro k'
  rw [AMap.get?_put]
  split
  · next heq =>
    subst heq
    refine ⟨by rw [← (h k').1, hk]; rfl, fun o2 ho2 => ?_⟩
    cases ho2
    obtain ⟨o1, h1, h2, h3⟩ := (h k').2 op hk
    refine ⟨o1, h1, h2, fun x hx => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact h3 x hx
    · exact Or.inr hx
  · exact h k'

/-- A new read (`N = maxN + 1`, a fresh key), after the loop over the writes. -/
theorem CoordOK.newRead (h : CoordOK mx oq ws rs u) (hmx : mx.toNat < 24) (rid cid : w32)
    (rop : ReadOp) (hf : FreshR rop) (hn : rop.n = mx + 1) {oq2 : AMap 32 OngoingOp}
    (hext : OqExt (mx + 1) (oq.put (mx + 1) ⟨rid, cid, true, []⟩) oq2) :
    CoordOK (mx + 1) oq2 ws (rs.put (shiftInts rid cid) rop) ((cid, rid) :: u) := by
  have hN : (mx + 1).toNat = mx.toNat + 1 := by
    rw [BitVec.toNat_add]; simp; omega
  have hne : ∀ k : w32, k.toNat ≤ mx.toNat → k ≠ mx + 1 := by
    intro k hk he; rw [he, hN] at hk; omega
  -- every key of oq2 that is a read's in oq1 is a read's
  have hread : ∀ k o', oq2.get? k = some o' → ∀ o1, (oq.put (mx + 1) ⟨rid, cid, true, []⟩).get? k = some o1 →
      o1.isRead = true → o'.isRead = true := by
    intro k o' h2 o1 h1 hr
    obtain ⟨o1', h1', e, _⟩ := (hext k).2 o' h2
    rw [h1] at h1'; cases h1'; rw [e, hr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k o hk
    obtain ⟨o1, h1, e1, e2⟩ := (hext k).2 o hk
    rw [AMap.get?_put] at h1
    split at h1
    · next heq =>
      cases h1; subst heq
      refine ⟨Nat.le_refl _, fun k' hk' => ?_⟩
      rcases e2 k' hk' with hx | hx
      · simp at hx
      · subst hx
        refine ⟨Nat.le_refl _, fun o' ho' => hread _ o' ho' ⟨rid, cid, true, []⟩ (by rw [AMap.get?_put]; simp) rfl⟩
    · obtain ⟨a, b⟩ := h.oreq k o1 h1
      refine ⟨by omega, fun k' hk' => ?_⟩
      rcases e2 k' hk' with hx | hx
      · obtain ⟨b1, b2⟩ := b k' hx
        refine ⟨by omega, fun o' ho' => ?_⟩
        obtain ⟨o1', h1', _, _⟩ := (hext k').2 o' ho'
        rw [AMap.get?_put, if_neg (hne _ b1)] at h1'
        exact hread _ o' ho' o1' (by rw [AMap.get?_put, if_neg (hne _ b1)]; exact h1') (b2 o1' h1')
      · subst hx
        refine ⟨Nat.le_refl _, fun o' ho' => hread _ o' ho' ⟨rid, cid, true, []⟩ (by rw [AMap.get?_put]; simp) rfl⟩
  · intro e he
    obtain ⟨a, ⟨o, ho, hro⟩, c, d, f, g⟩ := h.wops e he
    have h1 : (oq.put (mx + 1) ⟨rid, cid, true, []⟩).get? e.2.n = some o := by
      rw [AMap.get?_put, if_neg (hne _ a)]; exact ho
    have hs := (hext e.2.n).1
    rw [h1] at hs
    obtain ⟨o2, ho2⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨o1, h1', e1, _⟩ := (hext e.2.n).2 o2 ho2
    rw [h1] at h1'; cases h1'
    exact ⟨by omega, ⟨o2, ho2, by rw [e1, hro]⟩, c, d, f, by simp [g]⟩
  · exact h.wopsN
  · intro id r' hr'
    rw [AMap.get?_put] at hr'
    split at hr'
    · cases hr'
      refine ⟨hf, by rw [hn, hN]; omega, fun o ho => ?_⟩
      exact hread _ o ho ⟨rid, cid, true, []⟩ (by rw [hn, AMap.get?_put]; simp) rfl
    · obtain ⟨a, b, c⟩ := h.rops id r' hr'
      refine ⟨a, by omega, fun o ho => ?_⟩
      obtain ⟨o1, h1, e1, _⟩ := (hext r'.n).2 o ho
      rw [AMap.get?_put, if_neg (hne _ b)] at h1
      rw [e1]; exact c o1 h1

end

end Perennial.gryff.pure.tot
