/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c2/ExecModel.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c2: `handleExecuted`'s cases (pure)
-/
module

public import Dsverify.Proof.gryff.H2c.CommitModel

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Perennial.gryff.model

/-- The bookkeeping after an `Executed` notice. -/
def exLB (lb : LB) : LB := { lb with numReplicasExecuted := lb.numReplicasExecuted + 1 }

/-- The leader replies (the first time a majority executed). -/
def exReply (lb : LB) : Bool := !lb.repliedClient && sge (lb.numReplicasExecuted + 1) 2

theorem handleExecuted_cases (s s' : RState) (outs : List Out) (m : ExecutedM)
    (h : handleExecuted s m = .ok (s', outs)) :
    inBox m.replica m.inst = true ∧
    ((s.inst m.replica m.inst = none ∧ s' = s ∧ outs = []) ∨
     (∃ c, s.inst m.replica m.inst = some c ∧
      ((c.lb = none ∧ s' = s ∧ outs = []) ∨
       (∃ lb, c.lb = some lb ∧
        ((exReply lb = true ∧ ∃ p, lb.clientProposals.head? = some p ∧
            s' = s.setInst m.replica m.inst { c with lb := some { exLB lb with repliedClient := true } } ∧
            outs = [.ext (.rmwReply p.client p.cmdId 1)]) ∨
         (exReply lb = false ∧ s' = s.setInst m.replica m.inst { c with lb := some (exLB lb) } ∧
            outs = [])))))) := by
  unfold handleExecuted at h
  have hbox : inBox m.replica m.inst = true := by
    cases hc : inBox m.replica m.inst
    · simp only [hc] at h; simp at h; cases h
    · rfl
  simp only [hbox, Bool.not_true] at h
  refine ⟨hbox, ?_⟩
  rcases hc : s.inst m.replica m.inst with _ | c
  · simp only [hc] at h
    simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact .inl ⟨rfl, h.1.symm, h.2.symm⟩
  simp only [hc] at h
  refine .inr ⟨c, rfl, ?_⟩
  rcases hlb : c.lb with _ | lb
  · simp only [hlb] at h
    simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact .inl ⟨rfl, h.1.symm, h.2.symm⟩
  simp only [hlb] at h
  refine .inr ⟨lb, rfl, ?_⟩
  by_cases hr : exReply lb = true
  · have hr' : (!lb.repliedClient && sge (lb.numReplicasExecuted + 1) 2) = true := hr
    simp only [hr', ↓reduceIte] at h
    rcases hp : lb.clientProposals.head? with _ | p
    · simp only [hp] at h; simp at h; cases h
    simp only [hp, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact .inl ⟨hr, p, rfl, h.1.symm, h.2.symm⟩
  · have hr' : (!lb.repliedClient && sge (lb.numReplicasExecuted + 1) 2) = false :=
      Bool.eq_false_iff.2 hr
    simp only [hr', Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    exact .inr ⟨Bool.eq_false_iff.2 hr, h.1.symm, h.2.symm⟩

end Perennial.gryff.replica2
