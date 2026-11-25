/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c2/PARModel.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c2: `stepPreAcceptReply`'s cases (pure)
-/
module

public import Dsverify.Proof.gryff.H2c2.PAOKModel

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Perennial.gryff.model

/-- The leader's copy after merging a reply's attributes (and its base, if newer). -/
def prC (c : Copy) (m : PreAcceptReplyM) (seq : w32) (deps : Deps) : Copy :=
  if m.base.t.gt c.base.t then { c with seq, deps, base := m.base } else { c with seq, deps }

/-- Whether the reply agreed (`equal`, false when the reply's base is newer). -/
def prEq (c : Copy) (m : PreAcceptReplyM) (eq0 : Bool) : Bool :=
  if m.base.t.gt c.base.t then false else eq0

/-- The bookkeeping after a positive reply. -/
def prLB (lb : LB) (eq : Bool) : LB :=
  { lb with preAcceptOKs := lb.preAcceptOKs + 1, allEqual := lb.allEqual && eq }

theorem stepPreAcceptReply_cases (s s' : RState) (outs : List Out) (m : PreAcceptReplyM)
    (h : stepPreAcceptReply s m = .ok (s', outs)) :
    inBox m.replica m.inst = true ∧ ∃ c, s.inst m.replica m.inst = some c ∧
    (((c.status ≠ St.PREACCEPTED ∨ c.ballot ≠ m.ballot) ∧ s' = s ∧ outs = []) ∨
     (c.status = St.PREACCEPTED ∧ c.ballot = m.ballot ∧ ∃ lb, c.lb = some lb ∧
      ((m.ok = FALSE ∧ outs = [] ∧
          s' = s.setInst m.replica m.inst { c with lb := some (arNack lb m.ballot) }) ∨
       (m.ok ≠ FALSE ∧ ∃ seq deps eq0, mergeAttributes s c.seq c.deps m.seq m.deps = (seq, deps, eq0) ∧
        ((paFast (prC c m seq deps) (prLB lb (prEq c m eq0)) = true ∧
            leaderCommit s m.replica m.inst (prC c m seq deps) (prLB lb (prEq c m eq0)) =
              .ok (s', outs)) ∨
         (paFast (prC c m seq deps) (prLB lb (prEq c m eq0)) = false ∧
            sge (prLB lb (prEq c m eq0)).preAcceptOKs NHALF = true ∧
            s' = s.setInst m.replica m.inst (paAcc (prC c m seq deps) (prLB lb (prEq c m eq0))) ∧
            bcastAccept s' m.replica m.inst c.ballot c.cmds (prC c m seq deps).seq
              (prC c m seq deps).deps (prC c m seq deps).base = some outs) ∨
         (paFast (prC c m seq deps) (prLB lb (prEq c m eq0)) = false ∧
            sge (prLB lb (prEq c m eq0)).preAcceptOKs NHALF = false ∧
            s' = s.setInst m.replica m.inst
              { prC c m seq deps with lb := some (prLB lb (prEq c m eq0)) } ∧ outs = [])))))) := by
  unfold stepPreAcceptReply at h
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
  by_cases hst : c.status = St.PREACCEPTED
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
        rw [← h1, hst, hb]; rfl
      · refine .inr ⟨hok, ?_⟩
        simp only [hok, ↓reduceIte] at h
        rcases hm : mergeAttributes s c.seq c.deps m.seq m.deps with ⟨seq, deps, eq0⟩
        refine ⟨seq, deps, eq0, rfl, ?_⟩
        rw [hm] at h
        by_cases hg : m.base.t.gt c.base.t = true
        all_goals
          simp only [hg, ↓reduceIte, Bool.false_eq_true] at h
          simp only [prC, prEq, prLB, paFast, paAcc, hg, ↓reduceIte, Bool.false_eq_true, hb]
          split at h
          · exact .inl ⟨by assumption, h⟩
          · split at h
            · split at h
              · rename_i hf hn _ os hos
                simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact .inr (.inl ⟨Bool.eq_false_iff.2 hf, hn, rfl, by simpa [hst] using hos⟩)
              · cases h
            · rename_i hf hn
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .inr (.inr ⟨Bool.eq_false_iff.2 hf, Bool.eq_false_iff.2 hn, by rw [hst], rfl⟩)
    · left
      simp only [hst, hb, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq, Bool.false_eq_true] at h
      exact ⟨.inr hb, h.1.symm, h.2.symm⟩
  · left
    simp only [hst, ne_eq, not_false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq, Bool.false_eq_true] at h
    exact ⟨.inl hst, h.1.symm, h.2.symm⟩

end Perennial.gryff.replica2
