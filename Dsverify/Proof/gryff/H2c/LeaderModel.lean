/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c/LeaderModel.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c: the commit at the proposer (`leaderCommit`) and `stepAcceptReply`'s cases (pure)
-/
module

public import Dsverify.Proof.gryff.H2c.CommitModel

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Perennial.gryff.model

/-- G11's condition: the committed value is not the clients'. -/
def lcRe (c : Copy) (lb : LB) : Prop :=
  lb.clientProposals ≠ [] ∧ c.cmds.length < lb.clientProposals.length

instance (c : Copy) (lb : LB) : Decidable (lcRe c lb) := by unfold lcRe; infer_instance

/-- The committed copy. -/
def lcC1 (c : Copy) (lb : LB) : Copy := { c with status := St.COMMITTED, lb := some lb }

/-- The state after G11's re-proposal (from the state `s2` after `updateCommitted`). -/
def lcS3 (s2 : RState) (q i : w32) (c : Copy) (lb : LB) : RState :=
  if lcRe c lb then
    { s2 with proposeQ := s2.proposeQ ++ lb.clientProposals }.setInst q i
      { lcC1 c lb with lb := none }
  else s2

theorem leaderCommit_cases (s s' : RState) (outs : List Out) (q i : w32) (c : Copy) (lb : LB)
    (h : leaderCommit s q i c lb = .ok (s', outs)) :
    ∃ s2, updateCommitted (s.setInst q i (lcC1 c lb)) q = some s2 ∧ s' = lcS3 s2 q i c lb ∧
      bcastCommit s' q i c.cmds c.seq c.deps c.base = some outs := by
  unfold leaderCommit at h
  simp only at h
  split at h
  · rename_i s2 hs2
    refine ⟨s2, hs2, ?_⟩
    by_cases hre : lcRe c lb
    · have hre' : lb.clientProposals ≠ [] ∧ c.cmds.length < lb.clientProposals.length := hre
      simp only [hre', ne_eq, not_false_eq_true, and_self, ↓reduceIte] at h
      split at h
      · rename_i os hos
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by simp [lcS3, hre, lcC1], ?_⟩
        simpa using hos
      · cases h
    · have hre' : ¬ (lb.clientProposals ≠ [] ∧ c.cmds.length < lb.clientProposals.length) := hre
      simp only [hre', ↓reduceIte] at h
      split at h
      · rename_i os hos
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by simp [lcS3, hre], ?_⟩
        simpa using hos
      · cases h
  · cases h

end Perennial.gryff.replica2

namespace Perennial.gryff.replica2

open Perennial.gryff.model

/-- A refusal's bookkeeping. -/
def arNack (lb : LB) (b : w32) : LB :=
  { lb with nacks := lb.nacks + 1,
            maxRecvBallot := if sgt b lb.maxRecvBallot then b else lb.maxRecvBallot }

theorem stepAcceptReply_cases (s s' : RState) (outs : List Out) (m : AcceptReplyM)
    (h : stepAcceptReply s m = .ok (s', outs)) :
    inBox m.replica m.inst = true ∧ ∃ c, s.inst m.replica m.inst = some c ∧
    (((c.status ≠ St.ACCEPTED ∨ c.ballot ≠ m.ballot) ∧ s' = s ∧ outs = []) ∨
     (c.status = St.ACCEPTED ∧ c.ballot = m.ballot ∧ ∃ lb, c.lb = some lb ∧
      ((m.ok = FALSE ∧ outs = [] ∧ s' = s.setInst m.replica m.inst
          { c with lb := some (arNack lb m.ballot) }) ∨
       (m.ok ≠ FALSE ∧ sgt (lb.acceptOKs + 1 + 1) NHALF = false ∧ outs = [] ∧
          s' = s.setInst m.replica m.inst { c with lb := some { lb with acceptOKs := lb.acceptOKs + 1 } }) ∨
       (m.ok ≠ FALSE ∧ sgt (lb.acceptOKs + 1 + 1) NHALF = true ∧
          leaderCommit s m.replica m.inst c { lb with acceptOKs := lb.acceptOKs + 1 } =
            .ok (s', outs))))) := by
  unfold stepAcceptReply at h
  have hbox : inBox m.replica m.inst = true := by
    cases hc : inBox m.replica m.inst
    · simp only [hc] at h; simp at h; cases h
    · rfl
  simp only [hbox, Bool.not_true] at h
  refine ⟨hbox, ?_⟩
  rcases hc : s.inst m.replica m.inst with _ | c
  · simp only [hc] at h; simp at h
  refine ⟨c, rfl, ?_⟩
  simp only [hc] at h
  by_cases hst : c.status = St.ACCEPTED
  · by_cases hb : c.ballot = m.ballot
    · right
      refine ⟨hst, hb, ?_⟩
      rcases hlb : c.lb with _ | lb
      · simp [hst, hb, hlb] at h
      refine ⟨lb, rfl, ?_⟩
      simp only [hst, hb, hlb, ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true] at h
      by_cases hok : m.ok = FALSE
      · simp only [hok, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        refine .inl ⟨hok, h2.symm, ?_⟩
        rw [← h1]; congr 1
        cases c; simp only at hst hb hlb; subst hst hb hlb; rfl
      · simp only [hok, ↓reduceIte] at h
        by_cases hc2 : sgt (lb.acceptOKs + 1 + 1) NHALF = true
        · simp only [hc2, ↓reduceIte] at h
          refine .inr (.inr ⟨hok, hc2, ?_⟩)
          rw [← h]
        · simp only [hc2, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          refine .inr (.inl ⟨hok, by simpa using hc2, h2.symm, ?_⟩)
          rw [← h1]; congr 1
          cases c; simp only at hst hb hlb; subst hst hb hlb; rfl
    · left
      simp only [hst, hb, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq, Bool.false_eq_true] at h
      exact ⟨.inr hb, h.1.symm, h.2.symm⟩
  · left
    simp only [hst, ne_eq, not_false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq, Bool.false_eq_true] at h
    exact ⟨.inl hst, h.1.symm, h.2.symm⟩

end Perennial.gryff.replica2
