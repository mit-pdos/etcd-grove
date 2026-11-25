/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2b/Phase1Model.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2b: `startPhase1` / `handlePropose`, the model side (pure)

The model's `startPhase1` cut along the Go code: the initial dependencies, `updateAttributes`, the
new copy, `updateConflicts`, `bcastPreAccept`.
-/
module

public import Dsverify.Proof.gryff.Model.Step

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2.h2b

open Perennial.gryff.model

/-- The dependencies `startPhase1` starts from (`-1` for each replica; G32: `instance - 1` on the
instance's row when it is another replica's). -/
def sp1Deps0 (s : RState) (replica islot : w32) : Deps :=
  if replica ≠ s.id then Deps.setAt ([-1, -1, -1, 0, 0] : Deps) replica.toNat (islot - 1)
  else [-1, -1, -1, 0, 0]

/-- The leader's bookkeeping `startPhase1` creates. -/
def sp1LB (prs : List Proposal) (deps : Deps) : LB :=
  { clientProposals := prs, maxRecvBallot := 0, prepareOKs := 0, allEqual := true,
    preAcceptOKs := 0, acceptOKs := 0, nacks := 0, originalDeps := deps,
    committedDeps := [-1, -1, -1, -1, -1], recoveryInst := none, preparing := false,
    numReplicasExecuted := 0, repliedClient := false }

/-- The copy `startPhase1` creates. -/
def sp1Copy (replica islot ballot : w32) (prs : List Proposal) (cmds : List Cmd) (seq : w32)
    (deps : Deps) (base : ValTag) : Copy :=
  { cmds, ballot, status := St.PREACCEPTED, seq, deps, base, lb := some (sp1LB prs deps),
    slot := islot, leader := replica, vbal := ballot }

/-- **`startPhase1`'s result**, by phase. -/
theorem startPhase1_cases (s s' : RState) (replica islot ballot : w32) (prs : List Proposal)
    (cmds : List Cmd) (outs : List Out)
    (h : startPhase1 s replica islot ballot prs cmds = .ok (s', outs)) :
    ∃ (seq : w32) (deps : Deps) (ch : Bool),
      updateAttributes s cmds 0 (sp1Deps0 s replica islot) replica = some (seq, deps, ch) ∧
      cmds ≠ [] ∧ inBox replica islot = true ∧
      s' = updateConflicts (s.setInst replica islot
        (sp1Copy replica islot ballot prs cmds seq deps s.storeVT)) cmds replica islot seq ∧
      bcastPreAccept (updateConflicts (s.setInst replica islot
        (sp1Copy replica islot ballot prs cmds seq deps s.storeVT)) cmds replica islot seq)
        replica islot ballot cmds seq deps s.storeVT = some outs := by
  unfold startPhase1 at h
  have hd : sp1Deps0 s replica islot = (if replica ≠ s.id then
      Deps.setAt ([-1, -1, -1, 0, 0] : Deps) replica.toNat (islot - 1) else [-1, -1, -1, 0, 0]) := rfl
  by_cases hr : replica ≠ s.id
  all_goals first | rw [if_pos hr] at h hd | rw [if_neg hr] at h hd
  all_goals
    dsimp only at h
    rw [← hd] at h
    split at h
    · next seq deps ch hu =>
      split at h
      · next c0 hc0 =>
        by_cases hb : inBox replica islot = true
        · simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          split at h
          · next outs' ho =>
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨seq, deps, ch, hu, ?_, hb, rfl, ho⟩
            rintro rfl; simp at hc0
          · cases h
        · simp only [hb, Bool.not_false, ↓reduceIte] at h
          cases h
      · cases h
    · cases h

/-- `updateConflicts` writes the conflict tables only. -/
theorem updateConflicts_shape (s : RState) (cmds : List Cmd) (q i seq : w32) :
    ∃ cf ms, updateConflicts s cmds q i seq = { s with conf := cf, maxSeqK0 := ms } := by
  unfold updateConflicts
  simp only [Id.run]
  induction cmds generalizing s with
  | nil => exact ⟨s.conf, s.maxSeqK0, rfl⟩
  | cons c cs ih =>
    simp only [List.forIn_cons]
    obtain ⟨cf, ms, h⟩ := ih { s with conf := _, maxSeqK0 := _ }
    exact ⟨cf, ms, by simpa using h⟩

theorem updateConflicts_inst (s : RState) (cmds : List Cmd) (q i seq : w32) :
    (updateConflicts s cmds q i seq).inst = s.inst := by
  obtain ⟨cf, ms, h⟩ := updateConflicts_shape s cmds q i seq; rw [h]

theorem updateConflicts_id (s : RState) (cmds : List Cmd) (q i seq : w32) :
    (updateConflicts s cmds q i seq).id = s.id := by
  obtain ⟨cf, ms, h⟩ := updateConflicts_shape s cmds q i seq; rw [h]

/-- Setting a slot to the copy it holds. -/
theorem setInst_self (s : RState) (q i : w32) (c : Copy) (h : s.inst q i = some c) :
    s.setInst q i c = s := by
  cases s
  simp only [RState.setInst, RState.mk.injEq, and_true, true_and]
  funext q' i'
  by_cases e : q' = q ∧ i' = i
  · obtain ⟨rfl, rfl⟩ := e; simp only [and_self, ↓reduceIte]; exact h.symm
  · simp only [e, ↓reduceIte]

theorem setInst_inst_self (s : RState) (q i : w32) (c : Copy) : (s.setInst q i c).inst q i = some c := by
  simp [RState.setInst]

theorem setInst_id (s : RState) (q i : w32) (c : Copy) : (s.setInst q i c).id = s.id := rfl

end Perennial.gryff.replica2.h2b
