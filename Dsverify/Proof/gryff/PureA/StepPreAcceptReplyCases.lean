/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepPreAcceptReplyCases.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1c, internal: the succeeding paths of `stepPreAcceptReply` (`stepPreAcceptReply_cases`) and
`stepPreAcceptOK` (`stepPreAcceptOK_cases`), and the shape of `leaderCommit`.
-/
module

public import Dsverify.Proof.gryff.PureA.StepPreAccept

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.SPA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

/-- The merged copy `c2` of `handlePreAcceptReply` (attributes merged, base raised to the reply's
when larger). -/
structure Merged (s : RState) (m : PreAcceptReplyM) (c c2 : Copy) : Prop where
  cmds : c2.cmds = c.cmds
  ballot : c2.ballot = c.ballot
  vbal : c2.vbal = c.vbal
  status : c2.status = c.status
  seq : c2.seq = (mergeAttributes s c.seq c.deps m.seq m.deps).1
  deps : c2.deps = (mergeAttributes s c.seq c.deps m.seq m.deps).2.1
  lb : c2.lb = c.lb
  base : (m.base.t.gt c.base.t = true ∧ c2.base = m.base) ∨
    (m.base.t.gt c.base.t = false ∧ c2.base = c.base)

/-- The bookkeeping after an OK. -/
structure LbOK (lb lb2 : LB) : Prop where
  preparing : lb2.preparing = lb.preparing
  prepareOKs : lb2.prepareOKs = lb.prepareOKs
  recoveryInst : lb2.recoveryInst = lb.recoveryInst
  oks : lb2.preAcceptOKs = lb.preAcceptOKs + 1

/-- The bookkeeping after a NACK (or nothing read by `CInv` changed). -/
structure LbSame (lb lb2 : LB) : Prop where
  preparing : lb2.preparing = lb.preparing
  prepareOKs : lb2.prepareOKs = lb.prepareOKs
  recoveryInst : lb2.recoveryInst = lb.recoveryInst
  oks : lb2.preAcceptOKs = lb.preAcceptOKs

def PARCases (s : RState) (m : PreAcceptReplyM) (s' : RState) (o : List Out) : Prop :=
  (s' = s ∧ o = []) ∨
  ∃ c lb, s.inst m.replica m.inst = some c ∧ c.status = St.PREACCEPTED ∧ c.ballot = m.ballot ∧
    c.lb = some lb ∧
    ((m.ok = FALSE ∧ o = [] ∧ ∃ lb', s' = s.setInst m.replica m.inst { c with lb := some lb' } ∧
        LbSame lb lb') ∨
     (m.ok ≠ FALSE ∧ ∃ c2 lb2,
       ((isInitialBallot c.ballot = true ∧ (mergeAttributes s c.seq c.deps m.seq m.deps).2.2 = true ∧
          m.base.t.gt c.base.t = false ∧ leaderCommit s m.replica m.inst c2 lb2 = .ok (s', o)) ∨
        (s' = s.setInst m.replica m.inst
            { c2 with status := St.ACCEPTED, vbal := c.ballot, lb := some lb2 } ∧
          bcastAccept s' m.replica m.inst c.ballot c2.cmds c2.seq c2.deps c2.base = some o) ∨
        (sge (lb.preAcceptOKs + 1) NHALF = false ∧ o = [] ∧
          s' = s.setInst m.replica m.inst { c2 with lb := some lb2 })) ∧
       Merged s m c c2 ∧ LbOK lb lb2))

/-- The merged copy with base `b`. -/
def mcopy (s : RState) (m : PreAcceptReplyM) (c : Copy) (b : ValTag) : Copy :=
  { c with seq := (mergeAttributes s c.seq c.deps m.seq m.deps).1,
           deps := (mergeAttributes s c.seq c.deps m.seq m.deps).2.1, base := b }

/-- The bookkeeping after an OK. -/
def lbOK' (lb : LB) (ae : Bool) : LB := { lb with preAcceptOKs := lb.preAcceptOKs + 1, allEqual := ae }

theorem fast_cond {x y : w64} {a e z : Bool} (h : (sge x y && (a && e) && z) = true) :
    e = true ∧ z = true := by
  simp only [Bool.and_eq_true] at h; exact ⟨h.1.2.2, h.2⟩

set_option maxRecDepth 20000 in
theorem stepPreAcceptReply_cases {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) : inBox m.replica m.inst = true ∧ PARCases s m s' o := by
  refine ⟨?_, ?_⟩
  · unfold stepPreAcceptReply at h; peel h
    all_goals (simpa using ‹¬(!inBox _ _) = true›)
  unfold stepPreAcceptReply at h
  rcases hc : s.inst m.replica m.inst with _ | c <;> simp only [hc] at h
  · peel h
  rcases hl : c.lb with _ | lb <;> simp only [hl] at h <;> peel h
  all_goals first
    | (cases h; exact Or.inl ⟨rfl, rfl⟩)
    | (cases h
       refine Or.inr ⟨c, lb, hc, Decidable.of_not_not (by assumption), Decidable.of_not_not (by assumption),
         hl, Or.inl ⟨asm, rfl, _, rfl, ?_⟩⟩
       exact ⟨rfl, rfl, rfl, rfl⟩
       done)
    | exact Bool.noConfusion (fast_cond asm).1
    | (refine Or.inr ⟨c, lb, hc, Decidable.of_not_not (by assumption), Decidable.of_not_not (by assumption),
         hl, Or.inr ⟨asm, ?_⟩⟩
       first
         | exact ⟨mcopy s m c _, lbOK' lb _,
             Or.inl ⟨(fast_cond asm).2, (fast_cond asm).1, nt asm, h⟩,
             ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by first | exact Or.inl ⟨asm, rfl⟩ | exact Or.inr ⟨nt asm, rfl⟩⟩,
             ⟨rfl, rfl, rfl, rfl⟩⟩
         | (cases h
            exact ⟨mcopy s m c _, lbOK' lb _,
             Or.inr (Or.inl ⟨rfl, (by assumption)⟩),
             ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by first | exact Or.inl ⟨asm, rfl⟩ | exact Or.inr ⟨nt asm, rfl⟩⟩,
             ⟨rfl, rfl, rfl, rfl⟩⟩)
         | (cases h
            exact ⟨mcopy s m c _, lbOK' lb _,
             Or.inr (Or.inr ⟨nt asm, rfl, rfl⟩),
             ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by first | exact Or.inl ⟨asm, rfl⟩ | exact Or.inr ⟨nt asm, rfl⟩⟩,
             ⟨rfl, rfl, rfl, rfl⟩⟩))

def PAOKCases (s : RState) (m : PreAcceptOKM) (s' : RState) (o : List Out) : Prop :=
  (s' = s ∧ o = []) ∨
  ∃ c lb, s.inst s.id m.inst = some c ∧ c.status = St.PREACCEPTED ∧ isInitialBallot c.ballot = true ∧
    c.lb = some lb ∧
    ((lb.allEqual = true ∧ leaderCommit s s.id m.inst c
        { lb with preAcceptOKs := lb.preAcceptOKs + 1 } = .ok (s', o)) ∨
     (s' = s.setInst s.id m.inst
        { c with status := St.ACCEPTED, vbal := c.ballot,
                 lb := some { lb with preAcceptOKs := lb.preAcceptOKs + 1 } } ∧
       bcastAccept s' s.id m.inst c.ballot c.cmds c.seq c.deps c.base = some o) ∨
     (sge (lb.preAcceptOKs + 1) NHALF = false ∧ o = [] ∧
       s' = s.setInst s.id m.inst { c with lb := some { lb with preAcceptOKs := lb.preAcceptOKs + 1 } }))

theorem fast_cond' {x y : w64} {a z : Bool} (h : (sge x y && a && z) = true) : a = true := by
  simp only [Bool.and_eq_true] at h; exact h.1.2

set_option maxRecDepth 20000 in
theorem stepPreAcceptOK_cases {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) : inBox s.id m.inst = true ∧ PAOKCases s m s' o := by
  refine ⟨?_, ?_⟩
  · unfold stepPreAcceptOK at h; peel h
    all_goals (simpa using ‹¬(!inBox _ _) = true›)
  unfold stepPreAcceptOK at h
  rcases hc : s.inst s.id m.inst with _ | c <;> simp only [hc] at h <;> peel h
  all_goals first
    | (cases h; exact Or.inl ⟨rfl, rfl⟩)
    | (refine Or.inr ⟨c, _, hc, Decidable.of_not_not (by assumption),
         by simpa using ‹¬(!isInitialBallot _) = true›, asm, ?_⟩
       first
         | exact Or.inl ⟨fast_cond' asm, asm⟩
         | (cases h; exact Or.inr (Or.inl ⟨rfl, (by assumption)⟩))
         | (cases h; exact Or.inr (Or.inr ⟨nt asm, rfl, rfl⟩)))

end Perennial.gryff.pureA.SPA
