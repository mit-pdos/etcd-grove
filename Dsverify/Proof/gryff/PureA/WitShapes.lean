/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/WitShapes.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AW, internal: handler facts the witness invariant needs beyond A1's shape lemmas (the new
copy's bookkeeping when the instance had no copy; `startPhase1`'s base and commands; the RMW's
`startPhase1`).
-/
module

public import Dsverify.Proof.gryff.PureA.WitDefs

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AW

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA

/-- `handleAccept` on an instance without copy makes a copy without bookkeeping. -/
theorem accept_lb_none {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) (hc : s.inst m.replica m.inst = none) :
    ∀ cp, s'.inst m.replica m.inst = some cp → cp.lb = none := by
  unfold stepAccept at h
  simp only [hc] at h
  peel h
  all_goals (cases h; intro cp hcp; rw [setInst_inst, if_pos ⟨rfl, rfl⟩] at hcp; cases hcp; rfl)

/-- `handlePreAccept` on an instance without copy makes a copy without bookkeeping. -/
theorem preAccept_lb_none {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) (hc : s.inst m.replica m.inst = none) :
    ∀ cp, s'.inst m.replica m.inst = some cp → cp.lb = none := by
  unfold stepPreAccept at h
  simp only [hc] at h
  peel h
  all_goals (
    cases h; intro cp hcp
    rw [(updateConflicts_inst _ _ _ _ _).1, setInst_inst, if_pos ⟨rfl, rfl⟩] at hcp
    cases hcp; rfl)

/-- `startPhase1`'s result, with the new copy's commands, base and candidate. -/
theorem sp1W {t t' : RState} {r i b : w32} {ps : List Proposal} {cs : List Cmd} {o : List Out}
    (h : startPhase1 t r i b ps cs = .ok (t', o)) :
    ∃ cp, (∀ q j, t'.inst q j = if q = r ∧ j = i then some cp else t.inst q j) ∧
      t'.id = t.id ∧ t'.crtInstance = t.crtInstance ∧
      cp.status = St.PREACCEPTED ∧ cp.ballot = b ∧ cp.cmds = cs ∧ cs ≠ [] ∧ cp.base = t.storeVT ∧
      (∀ lb, cp.lb = some lb → lb.recoveryInst = none) ∧
      ∀ (d : Fin 3) y, y ∈ A1b.sentR d o → ∃ x : PreAcceptM, y = .preAccept x ∧
        x.replica = r ∧ x.inst = i ∧ x.ballot = b ∧ x.base = cp.base ∧ rid32 d ≠ t.id := by
  unfold startPhase1 at h
  peel h
  all_goals (
    rename_i hbc
    cases h
    obtain ⟨e1, e2, e3⟩ := updateConflicts_inst (t.setInst r i _) cs r i _
    refine ⟨_, fun q' i' => by rw [e1]; rfl, e2, e3, rfl, rfl, rfl, ?_, rfl,
      fun lb hl => by cases hl; rfl, ?_⟩
    · intro hn; subst hn; simp at *
    intro d y hy
    obtain ⟨h1, h2⟩ := A1b.bcast_sent' hbc d y hy
    exact ⟨_, h1, rfl, rfl, rfl, rfl, by rw [e2] at h2; exact h2⟩)

/-- The RMW's `handlePropose` is `startPhase1` at slot `crt[id]` from a state with the same id,
store and copies, `crt[id]` raised. -/
theorem rmwW {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {oldV newV : w64}
    {o : List Out} (h : stepClientRMW s rid cid k d oldV newV = .ok (s', o)) :
    ∃ t ps cs, t.id = s.id ∧ t.tag = s.tag ∧ t.inst = s.inst ∧
      t.crtInstance = (s.setCrt s.id (s.crt s.id + 1)).crtInstance ∧
      startPhase1 t s.id (s.crt s.id) 0 ps cs = .ok (s', o) := by
  unfold stepClientRMW at h; peel h
  have h' := (handlePropose_ok h).2.2
  unfold handleProposeBody at h'
  dsimp only at h'
  refine ⟨_, _, _, ?_, ?_, ?_, ?_, h'⟩
  · rfl
  · rfl
  · rfl
  · simp only [RState.setCrt, RState.crt]

end Perennial.gryff.pureA.AW
