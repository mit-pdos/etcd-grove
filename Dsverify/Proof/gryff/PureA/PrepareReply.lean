/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/PrepareReply.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1, internal: `stepPrepareReply` (`Model/StepRecovery.lean`) restated through the candidate
updates of `Decide.lean` (`upd`), for the preservation proof of the agreement invariant.

`stepPrepareReply_main`: on the main path (a reply to a preparing, uncommitted copy, OK, at the
copy's ballot, not COMMITTED/EXECUTED), the step is `prMain`: the candidate becomes `upd ri m`; the
leader's pre-accepted reply (below ACCEPTED) only sets `leaderResponded` (`setLr`); with too few
replies nothing is decided; else `prDecide`: Accept of an ACCEPTED or counted-unchanged candidate
(G16, G24), the TryPreAccept branch (`dead`), a restart (`startPhase1`, G9/G32), or a no-op.
`stepPrepareReply_cases`: the other paths (no change, a NACK counted, G22's commit).
-/
module

public import Dsverify.Proof.gryff.PureA.Decide

@[expose] public section

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Perennial.gryff.pureA

open Perennial Perennial.gryff.model Perennial.gryff.pure

def prDecide (s : RState) (m : PrepareReplyM) (c : Copy) (lb : LB) : StepRes :=
  match lb.recoveryInst with
  | some ir =>
    if ir.status = St.ACCEPTED ∨
        (!ir.leaderResponded ∧ sge ir.preAcceptCount NHALF ∧ ir.status = St.PREACCEPTED_EQ) then
      let c' := { c with cmds := ir.cmds, seq := ir.seq, deps := ir.deps, base := ir.base,
                         status := St.ACCEPTED, vbal := c.ballot,
                         lb := some { lb with preparing := false } }
      let s := s.setInst m.replica m.inst c'
      match bcastAccept s m.replica m.inst c'.ballot c'.cmds c'.seq c'.deps c'.base with
      | some outs => .ok (s, outs)
      | _ => .error .dead
    else if !ir.leaderResponded ∧ sge ir.preAcceptCount ((NHALF + 1) / 2) then .error .dead
    else
      startPhase1 (s.setInst m.replica m.inst { c with lb := some { lb with preparing := false } })
        m.replica m.inst c.ballot lb.clientProposals ir.cmds
  | none =>
    let noopDeps := nildeps.setAt m.replica.toNat (m.inst - 1)
    let c' : Copy :=
      { cmds := [], ballot := c.ballot, status := St.ACCEPTED, seq := 0, deps := noopDeps,
        base := vt0, lb := some { lb with preparing := false }, slot := m.inst,
        leader := m.replica, vbal := c.ballot }
    let s := s.setInst m.replica m.inst c'
    match bcastAccept s m.replica m.inst c.ballot [] 0 noopDeps vt0 with
    | some outs => .ok (s, outs)
    | _ => .error .dead

def prMain (s : RState) (m : PrepareReplyM) (c : Copy) (lb0 : LB) : StepRes :=
  let ri := upd lb0.recoveryInst m
  let lb := { lb0 with prepareOKs := lb0.prepareOKs + 1, recoveryInst := ri }
  if (m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) ∧
      belowB (upd1 lb0.recoveryInst m) = true ∧ m.acceptorId = m.replica then
    match ri with
    | some r => .ok (s.setInst m.replica m.inst
        { c with lb := some { lb with recoveryInst := some (setLr r) } }, [])
    | _ => .error .dead
  else if slt lb.prepareOKs NHALF then .ok (s.setInst m.replica m.inst { c with lb := some lb }, [])
  else prDecide s m c lb

/-- `stepPrepareReply` on its main path is `prMain`. -/
theorem stepPrepareReply_main (s : RState) (m : PrepareReplyM) (c : Copy) (lb0 : LB)
    (hc : s.inst m.replica m.inst = some c) (hl : c.lb = some lb0) (hp : lb0.preparing = true)
    (hst : ¬ (c.status = St.COMMITTED ∨ c.status = St.EXECUTED)) (hok : m.ok ≠ FALSE)
    (hb : m.ballot = c.ballot) (hm : ¬ (m.status = St.COMMITTED ∨ m.status = St.EXECUTED))
    (hcmd : cmdsOk m.cmds = true) (hbox : inBox m.replica m.inst = true) :
    stepPrepareReply s m = prMain s m c lb0 := by
  unfold stepPrepareReply
  simp only [hcmd, hbox, hc, hl, hp, hst, hok, hb, hm, Bool.not_true, Bool.false_eq_true, ite_false,
    ne_eq, not_true_eq_false, not_false_eq_true]
  unfold prMain prDecide upd upd1 upd2 belowB unchangedB setLr
  have e1 : St.ACCEPTED ≠ St.PREACCEPTED := by decide
  have e2 : St.ACCEPTED ≠ St.PREACCEPTED_EQ := by decide
  have e3 : St.PREACCEPTED ≠ St.PREACCEPTED_EQ := by decide
  have e4 : slt St.ACCEPTED St.ACCEPTED = false := by decide
  have e5 : slt St.PREACCEPTED St.ACCEPTED = true := by decide
  have e6 : slt St.PREACCEPTED_EQ St.ACCEPTED = true := by decide
  have hsts : (m.status = St.ACCEPTED ∧ m.status ≠ St.PREACCEPTED ∧ m.status ≠ St.PREACCEPTED_EQ) ∨
      (m.status ≠ St.ACCEPTED ∧ m.status = St.PREACCEPTED ∧ m.status ≠ St.PREACCEPTED_EQ) ∨
      (m.status ≠ St.ACCEPTED ∧ m.status ≠ St.PREACCEPTED ∧ m.status = St.PREACCEPTED_EQ) ∨
      (m.status ≠ St.ACCEPTED ∧ m.status ≠ St.PREACCEPTED ∧ m.status ≠ St.PREACCEPTED_EQ) := by
    by_cases h1 : m.status = St.ACCEPTED
    · left; exact ⟨h1, fun h => e1 (h1 ▸ h), fun h => e2 (h1 ▸ h)⟩
    by_cases h2 : m.status = St.PREACCEPTED
    · right; left; exact ⟨h1, h2, fun h => e3 (h2 ▸ h)⟩
    by_cases h3 : m.status = St.PREACCEPTED_EQ
    · right; right; left; exact ⟨h1, h2, h3⟩
    · right; right; right; exact ⟨h1, h2, h3⟩
  rcases hri : lb0.recoveryInst with _ | r <;>
  rcases hsts with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
  simp [h1, h2, h3, hp, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm, pure, Except.pure, dead,
    FailM.failDead] <;> (try rfl) <;>
  (by_cases hx : r.status = St.ACCEPTED <;> by_cases hy : slt r.vbal m.vbal = true <;>
   by_cases hz : m.vbal = 0#32 <;> by_cases hw : m.acceptorId = m.replica <;>
   by_cases hv : sgt r.preAcceptCount 0#64 = true <;>
   by_cases hs : slt r.status St.ACCEPTED = true <;>
   simp only [hx, hy, hw, hv, hs] <;>
   simp [h1, h2, h3, hx, hy, hz, hw, hv, hs, e1, e2, e3, e4, e5, e6, e1.symm, e2.symm, e3.symm] <;> (try rfl))
/-- The paths of `stepPrepareReply` that succeed. -/
theorem stepPrepareReply_cases {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) :
    (s' = s ∧ o = []) ∨
    (∃ c lb0, s.inst m.replica m.inst = some c ∧ c.lb = some lb0 ∧
      s' = s.setInst m.replica m.inst { c with lb := some { lb0 with nacks := lb0.nacks + 1 } } ∧
      o = []) ∨
    (∃ c lb0, s.inst m.replica m.inst = some c ∧ c.lb = some lb0 ∧ lb0.preparing = true ∧
      ¬ (c.status = St.COMMITTED ∨ c.status = St.EXECUTED) ∧ m.ok ≠ FALSE ∧ m.ballot = c.ballot ∧
      (m.status = St.COMMITTED ∨ m.status = St.EXECUTED) ∧
      s' = s.setInst m.replica m.inst
        { cmds := m.cmds, ballot := c.ballot, status := St.COMMITTED, seq := m.seq, deps := m.deps,
          base := m.base, lb := none, slot := m.inst, leader := m.replica, vbal := c.ballot } ∧
      bcastCommit s' m.replica m.inst m.cmds m.seq m.deps m.base = some o) ∨
    (∃ c lb0, s.inst m.replica m.inst = some c ∧ c.lb = some lb0 ∧ lb0.preparing = true ∧
      ¬ (c.status = St.COMMITTED ∨ c.status = St.EXECUTED) ∧ m.ok ≠ FALSE ∧ m.ballot = c.ballot ∧
      ¬ (m.status = St.COMMITTED ∨ m.status = St.EXECUTED) ∧ cmdsOk m.cmds = true ∧
      inBox m.replica m.inst = true ∧ prMain s m c lb0 = .ok (s', o)) := by
  by_cases hcmd' : cmdsOk m.cmds = false
  · unfold stepPrepareReply at h; simp [hcmd', never, FailM.failNever, bind, Except.bind] at h
  have hcmd : cmdsOk m.cmds = true := by simpa using hcmd'
  by_cases hbox' : inBox m.replica m.inst = false
  · unfold stepPrepareReply at h; simp [hcmd, hbox', dead, FailM.failDead, bind, Except.bind] at h
  have hbox : inBox m.replica m.inst = true := by simpa using hbox'
  rcases hc : s.inst m.replica m.inst with _ | c
  · unfold stepPrepareReply at h; simp [hcmd, hbox, hc, dead, FailM.failDead] at h
  rcases hl : c.lb with _ | lb0
  · unfold stepPrepareReply at h; simp [hcmd, hbox, hc, hl, pure, Except.pure] at h
    rcases h with ⟨rfl, rfl⟩; exact Or.inl ⟨rfl, rfl⟩
  by_cases hp' : lb0.preparing = false
  · unfold stepPrepareReply at h; simp [hcmd, hbox, hc, hl, hp', pure, Except.pure] at h
    rcases h with ⟨rfl, rfl⟩; exact Or.inl ⟨rfl, rfl⟩
  have hp : lb0.preparing = true := by simpa using hp'
  by_cases hst : c.status = St.COMMITTED ∨ c.status = St.EXECUTED
  · unfold stepPrepareReply at h; simp only [hcmd, hbox, hc, hl, hp] at h
    simp [hst, pure, Except.pure] at h
    rcases h with ⟨rfl, rfl⟩; exact Or.inl ⟨rfl, rfl⟩
  by_cases hok : m.ok = FALSE
  · unfold stepPrepareReply at h; simp only [hcmd, hbox, hc, hl, hp] at h
    simp [hst, hok, pure, Except.pure] at h
    rcases h with ⟨rfl, rfl⟩; exact Or.inr (Or.inl ⟨c, lb0, rfl, hl, by simp [hp], rfl⟩)
  by_cases hb' : m.ballot ≠ c.ballot
  · unfold stepPrepareReply at h; simp only [hcmd, hbox, hc, hl, hp] at h
    simp [hst, hok, hb', pure, Except.pure] at h
    rcases h with ⟨rfl, rfl⟩; exact Or.inl ⟨rfl, rfl⟩
  have hb : m.ballot = c.ballot := by simpa using hb'
  by_cases hm : m.status = St.COMMITTED ∨ m.status = St.EXECUTED
  · refine Or.inr (Or.inr (Or.inl ⟨c, lb0, rfl, hl, hp, hst, hok, hb, hm, ?_⟩))
    unfold stepPrepareReply at h; simp only [hcmd, hbox, hc, hl, hp] at h
    simp only [hst, hok, hb, hm, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, ne_eq,
      not_true_eq_false] at h
    split at h
    · rename_i outs hbc
      simp [pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hbc⟩
    · simp [dead, FailM.failDead, bind, Except.bind] at h
  · refine Or.inr (Or.inr (Or.inr ⟨c, lb0, rfl, hl, hp, hst, hok, hb, hm, hcmd, hbox, ?_⟩))
    rw [← stepPrepareReply_main s m c lb0 hc hl hp hst hok hb hm hcmd hbox]; exact h

end Perennial.gryff.pureA
