/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c2/PAOKModel.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c2: `stepPreAcceptOK`'s cases (pure)
-/
module

public import Dsverify.Proof.gryff.H2c.LeaderModel

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Perennial.gryff.model

/-- The bookkeeping after a pre-accept OK. -/
def paokLB (lb : LB) : LB := { lb with preAcceptOKs := lb.preAcceptOKs + 1 }

/-- The fast-path condition (N = 3: `allCommitted` holds). -/
def paFast (c : Copy) (lb : LB) : Bool :=
  sge lb.preAcceptOKs (FPQ - 1) && lb.allEqual && isInitialBallot c.ballot

/-- The copy accepted at its own ballot (the slow path's start, G16). -/
def paAcc (c : Copy) (lb : LB) : Copy :=
  { c with status := St.ACCEPTED, vbal := c.ballot, lb := some lb }

theorem stepPreAcceptOK_cases (s s' : RState) (outs : List Out) (m : PreAcceptOKM)
    (h : stepPreAcceptOK s m = .ok (s', outs)) :
    inBox s.id m.inst = true ∧ ∃ c, s.inst s.id m.inst = some c ∧
    (((c.status ≠ St.PREACCEPTED ∨ isInitialBallot c.ballot = false) ∧ s' = s ∧ outs = []) ∨
     (c.status = St.PREACCEPTED ∧ isInitialBallot c.ballot = true ∧ ∃ lb, c.lb = some lb ∧
      ((paFast c (paokLB lb) = true ∧ leaderCommit s s.id m.inst c (paokLB lb) = .ok (s', outs)) ∨
       (paFast c (paokLB lb) = false ∧ sge (paokLB lb).preAcceptOKs NHALF = true ∧
          s' = s.setInst s.id m.inst (paAcc c (paokLB lb)) ∧
          bcastAccept s' s.id m.inst c.ballot c.cmds c.seq c.deps c.base = some outs) ∨
       (paFast c (paokLB lb) = false ∧ sge (paokLB lb).preAcceptOKs NHALF = false ∧
          s' = s.setInst s.id m.inst { c with lb := some (paokLB lb) } ∧ outs = [])))) := by
  unfold stepPreAcceptOK at h
  have hbox : inBox s.id m.inst = true := by
    cases hc : inBox s.id m.inst
    · simp only [hc] at h; simp at h; cases h
    · rfl
  simp only [hbox, Bool.not_true] at h
  refine ⟨hbox, ?_⟩
  rcases hc : s.inst s.id m.inst with _ | c
  · simp only [hc] at h; simp at h
  refine ⟨c, rfl, ?_⟩
  simp only [hc] at h
  by_cases hst : c.status = St.PREACCEPTED
  · by_cases hb : isInitialBallot c.ballot = true
    · right
      refine ⟨hst, hb, ?_⟩
      rcases hlb : c.lb with _ | lb
      · simp [hst, hb, hlb] at h
      refine ⟨lb, rfl, ?_⟩
      simp only [hst, hb, hlb, ne_eq, not_true_eq_false, ↓reduceIte, Bool.not_true,
        Bool.false_eq_true] at h
      by_cases hf : paFast c (paokLB lb) = true
      · have hf' : (sge (lb.preAcceptOKs + 1) (FPQ - 1) && lb.allEqual && true)
            = true := by have := hf; simp only [paFast, paokLB, hb] at this; simpa using this
        simp only [hf', ↓reduceIte] at h
        exact .inl ⟨hf, h⟩
      · have hf' : (sge (lb.preAcceptOKs + 1) (FPQ - 1) && lb.allEqual && true)
            = false := by
          have := Bool.eq_false_iff.2 hf; simp only [paFast, paokLB, hb] at this; simpa using this
        simp only [hf', Bool.false_eq_true, ↓reduceIte] at h
        by_cases hn : sge (paokLB lb).preAcceptOKs NHALF = true
        · have hn' : sge (lb.preAcceptOKs + 1) NHALF = true := hn
          simp only [hn', ↓reduceIte] at h
          split at h
          · rename_i os hos
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine .inr (.inl ⟨Bool.eq_false_iff.2 hf, hn, rfl, ?_⟩)
            simpa [paAcc, paokLB, model.RState.setInst] using hos
          · cases h
        · have hn' : sge (lb.preAcceptOKs + 1) NHALF = false := Bool.eq_false_iff.2 hn
          simp only [hn', Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine .inr (.inr ⟨Bool.eq_false_iff.2 hf, Bool.eq_false_iff.2 hn, ?_, rfl⟩)
          rw [hst]; rfl
    · left
      have hb' : isInitialBallot c.ballot = false := Bool.eq_false_iff.2 hb
      simp only [hst, hb', ne_eq, not_true_eq_false, ↓reduceIte, Bool.not_false, Bool.false_eq_true, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨.inr hb', h.1.symm, h.2.symm⟩
  · left
    simp only [hst, ne_eq, not_false_eq_true, ↓reduceIte, Bool.false_eq_true, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    exact ⟨.inl hst, h.1.symm, h.2.symm⟩

end Perennial.gryff.replica2
