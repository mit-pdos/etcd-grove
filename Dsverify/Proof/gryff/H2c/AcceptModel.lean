/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c/AcceptModel.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c: `stepAccept`'s cases (pure)
-/
module

public import Dsverify.Proof.gryff.H2c.CommitModel

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Perennial.gryff.model

/-- `handleAccept`'s state after the `crtInstance` update. -/
def acS1 (s : RState) (m : EAcceptM) : RState :=
  if sge m.inst (s.crt m.replica) then s.setCrt m.replica (m.inst + 1) else s

/-- The accepted copy (an existing one). -/
def acCopy (c : Copy) (m : EAcceptM) : Copy :=
  { c with status := St.ACCEPTED, ballot := m.ballot, vbal := m.ballot, cmds := m.cmds,
           seq := m.seq, deps := m.deps, base := m.base }

/-- The accepted copy (a new one). -/
def acNew (m : EAcceptM) : Copy :=
  { cmds := m.cmds, ballot := m.ballot, status := St.ACCEPTED, seq := m.seq, deps := m.deps,
    base := m.base, lb := none, slot := m.inst, leader := m.replica, vbal := m.ballot }

/-- The reply. -/
def acReply (m : EAcceptM) (ok : w8) (b : w32) : Msg :=
  .acceptReply { replica := m.replica, inst := m.inst, ok := ok, ballot := b }

section acCopy
variable (c : Copy) (m : EAcceptM)
@[simp] theorem acCopy_cmds : (acCopy c m).cmds = m.cmds := rfl
@[simp] theorem acCopy_ballot : (acCopy c m).ballot = m.ballot := rfl
@[simp] theorem acCopy_status : (acCopy c m).status = St.ACCEPTED := rfl
@[simp] theorem acCopy_seq : (acCopy c m).seq = m.seq := rfl
@[simp] theorem acCopy_deps : (acCopy c m).deps = m.deps := rfl
@[simp] theorem acCopy_base : (acCopy c m).base = m.base := rfl
@[simp] theorem acCopy_slot : (acCopy c m).slot = c.slot := rfl
@[simp] theorem acCopy_leader : (acCopy c m).leader = c.leader := rfl
@[simp] theorem acCopy_vbal : (acCopy c m).vbal = m.ballot := rfl
@[simp] theorem acCopy_lb : (acCopy c m).lb = c.lb := rfl
end acCopy

theorem acS1_sameOut (s : RState) (m : EAcceptM) : sameOut s (acS1 s m) := by
  unfold acS1; split
  · exact sameOut_setCrt _ _ _
  · exact sameOut_refl s

theorem stepAccept_cases (s s' : RState) (outs : List Out) (m : EAcceptM)
    (h : stepAccept s m = .ok (s', outs)) :
    cmdsOk m.cmds = true ∧ inBox m.replica m.inst = true ∧
    ((∃ c, s.inst m.replica m.inst = some c ∧
        (c.status = St.COMMITTED ∨ c.status = St.EXECUTED) ∧ s' = s ∧ outs = []) ∨
     (∃ c o, s.inst m.replica m.inst = some c ∧
        ¬ (c.status = St.COMMITTED ∨ c.status = St.EXECUTED) ∧ slt m.ballot c.ballot = true ∧
        sendPeer (acS1 s m) m.leaderId (acReply m FALSE c.ballot) = some o ∧
        s' = acS1 s m ∧ outs = [o]) ∨
     (∃ c o, s.inst m.replica m.inst = some c ∧
        ¬ (c.status = St.COMMITTED ∨ c.status = St.EXECUTED) ∧ slt m.ballot c.ballot = false ∧
        s' = (acS1 s m).setInst m.replica m.inst (acCopy c m) ∧
        sendPeer s' m.leaderId (acReply m TRUE m.ballot) = some o ∧ outs = [o]) ∨
     (∃ o, s.inst m.replica m.inst = none ∧
        s' = (acS1 s m).setInst m.replica m.inst (acNew m) ∧
        sendPeer s' m.leaderId (acReply m TRUE m.ballot) = some o ∧ outs = [o])) := by
  unfold stepAccept at h
  have hok : cmdsOk m.cmds = true := by
    cases hc : cmdsOk m.cmds
    · simp only [hc] at h; simp at h; cases h
    · rfl
  have hbox : inBox m.replica m.inst = true := by
    cases hc : inBox m.replica m.inst
    · simp only [hok, hc] at h; simp at h; cases h
    · rfl
  simp only [hok, hbox, Bool.not_true] at h
  refine ⟨hok, hbox, ?_⟩
  rcases hc : s.inst m.replica m.inst with _ | c
  · by_cases hsge : sge m.inst (s.crt m.replica) = true
    all_goals
      simp only [hc, hsge, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i o ho
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine .inr (.inr (.inr ⟨o, rfl, by simp [acS1, hsge, acNew], ?_, rfl⟩))
        simpa [acS1, hsge, acNew, acReply] using ho
      · cases h
  · by_cases hcm : c.status = St.COMMITTED ∨ c.status = St.EXECUTED
    · have : (if c.status = St.COMMITTED ∨ c.status = St.EXECUTED then
          (pure (s, []) : Except Fail (RState × List Out)) else pure (s, [])) = pure (s, []) := by
        split <;> rfl
      left
      refine ⟨c, rfl, hcm, ?_⟩
      rcases hcm with hcm | hcm <;> simp [hc, hcm] at h <;>
        (obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h); exact ⟨h1.symm, h2.symm⟩)
    · by_cases hsge : sge m.inst (s.crt m.replica) = true
      all_goals
        simp only [hc, hcm, hsge, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hb : slt m.ballot c.ballot = true
        · simp only [hb, ↓reduceIte] at h
          split at h
          · rename_i o ho
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine .inr (.inl ⟨c, o, rfl, hcm, hb, ?_, by simp [acS1, hsge], rfl⟩)
            simpa [acS1, hsge, acReply] using ho
          · simp [bind, Except.bind] at h
        · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
          split at h
          · rename_i o ho
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine .inr (.inr (.inl ⟨c, o, rfl, hcm, by simpa using hb,
              by simp [acS1, hsge, acCopy], ?_, rfl⟩))
            simpa [acS1, hsge, acCopy, acReply] using ho
          · cases h

end Perennial.gryff.replica2
