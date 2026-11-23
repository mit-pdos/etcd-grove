/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/PureWrite.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1b: inversions of the coordinator's write-reply steps (`stepWrite1Reply`,
`stepWrite2Reply`).
-/
module

public import Dsverify.Proof.gryff.H1.PureSC

@[expose] public section

namespace Perennial.gryff.replica2

open Perennial.gryff.model

/-- The write op after a Write2 reply (`m.applied`). -/
def w2Upd (w : WriteOp) (applied : w32) : WriteOp :=
  { w with numWrite2Replies := w.numWrite2Replies + 1,
           numWrite2Applies := if sgt applied 0 then w.numWrite2Applies + 1 else w.numWrite2Applies }

theorem stepWrite2Reply_inv (k : Fin 3) (s s' : RState) (m : Write2ReplyM) (outs : List Out)
    (h : stepR k s (.msg (.write2Reply m)) = .ok (s', outs)) :
    (s.wops.get? (shiftInts m.requestId m.clientId) = none ∧ s' = s ∧ outs = []) ∨
    ∃ w, s.wops.get? (shiftInts m.requestId m.clientId) = some w ∧
      ((sge (w2Upd w m.applied).numWrite2Replies (NHALF + 1) = true ∧ ∃ wt s2 outs2,
          w.writeTag = some wt ∧
          (if sge (w2Upd w m.applied).numWrite2Applies (NHALF + 1) = true
            then shortCircuit s w.n ⟨w.writeValue, wt⟩ false else some (s, [])) = some (s2, outs2) ∧
          s' = { s2 with wops := s2.wops.del (shiftInts m.requestId m.clientId),
                         ongoingReqs := s2.ongoingReqs.del w.n } ∧
          outs = outs2 ++ [.ext (.writeReply w.clientId w.requestId 1)]) ∨
       (sge (w2Upd w m.applied).numWrite2Replies (NHALF + 1) = false ∧
          s' = { s with wops := s.wops.put (shiftInts m.requestId m.clientId) (w2Upd w m.applied) } ∧
          outs = [])) := by
  simp only [stepR, stepWrite2Reply, bind, Except.bind, pure, Except.pure] at h
  rcases Option.eq_none_or_eq_some (s.wops.get? (shiftInts m.requestId m.clientId)) with hg | ⟨w, hg⟩
  · left
    simp only [hg, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨hg, h.1.symm, h.2.symm⟩
  · right
    refine ⟨w, hg, ?_⟩
    simp only [hg] at h
    by_cases hq : sge (w2Upd w m.applied).numWrite2Replies (NHALF + 1) = true
    · simp only [w2Upd] at hq
      simp only [hq, ↓reduceIte] at h
      left
      refine ⟨by simpa [w2Upd] using hq, ?_⟩
      rcases Option.eq_none_or_eq_some w.writeTag with hr | ⟨wt, hr⟩
      · simp only [hr] at h; cases h
      · simp only [hr] at h
        split at h
        · rename_i _ s2 outs2 hsc
          cases h
          exact ⟨wt, s2, outs2, hr, by simpa [w2Upd] using hsc, rfl, rfl⟩
        · cases h
    · simp only [w2Upd] at hq
      simp only [hq, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
      right
      exact ⟨by simpa [w2Upd] using hq, h.1.symm, by rw [← h.2]⟩

end Perennial.gryff.replica2
