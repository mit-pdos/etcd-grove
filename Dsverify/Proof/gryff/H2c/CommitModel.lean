/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c/CommitModel.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c: `stepCommit`'s cases (pure)
-/
module

public import Dsverify.Proof.gryff.Model.Step
public import Dsverify.Proof.gryff.PureL.StoreSteps

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Perennial.gryff.model

/-- `handleCommit`'s state after the `crtInstance` update. -/
def cmS1 (s : RState) (m : ECommitM) : RState :=
  if sge m.inst (s.crt m.replica) then s.setCrt m.replica (m.inst + 1) else s

/-- The re-proposal's condition (G44): the copy has client proposals and a no-op was committed. -/
def cmRe (c : Copy) (m : ECommitM) : Prop :=
  ∃ lb, c.lb = some lb ∧ lb.clientProposals ≠ [] ∧ m.cmds = []

instance (c : Copy) (m : ECommitM) : Decidable (cmRe c m) := by
  unfold cmRe
  rcases c.lb with _ | lb
  · exact isFalse (by simp)
  · exact if h : lb.clientProposals ≠ [] ∧ m.cmds = [] then isTrue ⟨lb, rfl, h⟩
      else isFalse (by rintro ⟨lb', h1, h2⟩; cases h1; exact h h2)

/-- The proposals re-proposed. -/
def cmProps (c : Copy) : List Proposal :=
  match c.lb with
  | some lb => lb.clientProposals
  | none => []

/-- The state after the re-proposal. -/
def cmS2 (s1 : RState) (c : Copy) (m : ECommitM) : RState :=
  if cmRe c m then { s1 with proposeQ := s1.proposeQ ++ cmProps c } else s1

/-- The committed copy (an existing one). -/
def cmCopy (c : Copy) (m : ECommitM) : Copy :=
  { (if cmRe c m then { c with lb := none } else c) with
      cmds := m.cmds, seq := m.seq, deps := m.deps, base := m.base, status := St.COMMITTED }

/-- The committed copy (a new one). -/
def cmNew (m : ECommitM) : Copy :=
  { cmds := m.cmds, ballot := 0, status := St.COMMITTED, seq := m.seq, deps := m.deps,
    base := m.base, lb := none, slot := m.inst, leader := m.replica, vbal := 0 }

/-- The fields outside the EPaxos part (the participant, the store, the coordinator, `ProposeChan`,
the ghost counters) agree. -/
def sameOut (s s' : RState) : Prop :=
  s'.id = s.id ∧ s'.val = s.val ∧ s'.tag = s.tag ∧ s'.ongoing = s.ongoing ∧ s'.maxN = s.maxN ∧
    s'.rops = s.rops ∧ s'.wops = s.wops ∧ s'.ongoingReqs = s.ongoingReqs ∧
    s'.proposeQ = s.proposeQ ∧ s'.nReqs = s.nReqs ∧ s'.used = s.used

theorem sameOut_refl (s : RState) : sameOut s s := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sameOut_trans {a b c : RState} (h1 : sameOut a b) (h2 : sameOut b c) : sameOut a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
    b7.trans a7, b8.trans a8, b9.trans a9, b10.trans a10, b11.trans a11⟩

theorem sameOut_setInst (s : RState) (q i : w32) (c : Copy) : sameOut s (s.setInst q i c) :=
  sameOut_refl s

theorem sameOut_setCrt (s : RState) (q x : w32) : sameOut s (s.setCrt q x) :=
  sameOut_refl s

theorem sameOut_updateConflicts (s : RState) (cmds : List Cmd) (q i sq : w32) :
    sameOut s (updateConflicts s cmds q i sq) := by
  unfold updateConflicts
  apply pure.forIn_id_inv (P := fun x : RState => sameOut s x) _ _ _ (sameOut_refl s)
  intro a b hb
  exact hb

theorem updateCommitted_eq {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    ∃ cu, s' = { s with committedUpTo := cu } := by
  unfold updateCommitted at h
  split at h
  · simp only [pure, Option.some.injEq] at h
    exact ⟨_, h.symm⟩
  · cases h

theorem sameOut_updateCommitted {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    sameOut s s' := by
  obtain ⟨cu, rfl⟩ := updateCommitted_eq h
  exact sameOut_refl s

theorem updateCommitted_inst {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    s'.inst = s.inst := by
  obtain ⟨cu, rfl⟩ := updateCommitted_eq h
  rfl

theorem cmS1_sameOut (s : RState) (m : ECommitM) : sameOut s (cmS1 s m) := by
  unfold cmS1; split
  · exact sameOut_setCrt _ _ _
  · exact sameOut_refl s

theorem cmS2_setInst (s1 : RState) (c : Copy) (m : ECommitM) (q i : w32) (c' : Copy) :
    (cmS2 s1 c m).setInst q i c' = { s1.setInst q i c' with proposeQ := (cmS2 s1 c m).proposeQ } := by
  unfold cmS2; split <;> rfl

section cmCopy
variable (c : Copy) (m : ECommitM)
@[simp] theorem cmCopy_cmds : (cmCopy c m).cmds = m.cmds := by unfold cmCopy; split <;> rfl
@[simp] theorem cmCopy_ballot : (cmCopy c m).ballot = c.ballot := by unfold cmCopy; split <;> rfl
@[simp] theorem cmCopy_status : (cmCopy c m).status = St.COMMITTED := by unfold cmCopy; split <;> rfl
@[simp] theorem cmCopy_seq : (cmCopy c m).seq = m.seq := by unfold cmCopy; split <;> rfl
@[simp] theorem cmCopy_deps : (cmCopy c m).deps = m.deps := by unfold cmCopy; split <;> rfl
@[simp] theorem cmCopy_base : (cmCopy c m).base = m.base := by unfold cmCopy; split <;> rfl
@[simp] theorem cmCopy_slot : (cmCopy c m).slot = c.slot := by unfold cmCopy; split <;> rfl
@[simp] theorem cmCopy_leader : (cmCopy c m).leader = c.leader := by unfold cmCopy; split <;> rfl
@[simp] theorem cmCopy_vbal : (cmCopy c m).vbal = c.vbal := by unfold cmCopy; split <;> rfl
@[simp] theorem cmCopy_lb : (cmCopy c m).lb = if cmRe c m then none else c.lb := by
  unfold cmCopy; split <;> rfl
end cmCopy

theorem stepCommit_cases (s s' : RState) (outs : List Out) (m : ECommitM)
    (h : stepCommit s m = .ok (s', outs)) :
    cmdsOk m.cmds = true ∧ inBox m.replica m.inst = true ∧ outs = [] ∧
    ((∃ c, s.inst m.replica m.inst = some c ∧ c.status = St.EXECUTED ∧ s' = cmS1 s m) ∨
     (∃ c, s.inst m.replica m.inst = some c ∧ c.status ≠ St.EXECUTED ∧
        updateCommitted ((cmS2 (cmS1 s m) c m).setInst m.replica m.inst (cmCopy c m)) m.replica =
          some s') ∨
     (s.inst m.replica m.inst = none ∧
        updateCommitted (updateConflicts ((cmS1 s m).setInst m.replica m.inst (cmNew m)) m.cmds
          m.replica m.inst m.seq) m.replica = some s')) := by
  unfold stepCommit at h
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
      · rename_i s0 hs0
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, .inr (.inr ⟨rfl, ?_⟩)⟩
        simpa [cmS1, hsge, cmNew] using hs0
      · cases h
  · by_cases hsge : sge m.inst (s.crt m.replica) = true
    all_goals
      by_cases hx : c.status = St.EXECUTED
      · simp only [hc, hsge, hx, Bool.false_eq_true, ↓reduceIte] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, .inl ⟨c, rfl, hx, by simp [cmS1, hsge]⟩⟩
      · simp only [hc, hsge, hx, Bool.false_eq_true, ↓reduceIte] at h
        rcases hlb : c.lb with _ | lb
        · simp only [hlb] at h
          split at h
          · rename_i s0 hs0
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hre : ¬ cmRe c m := by simp [cmRe, hlb]
            refine ⟨rfl, .inr (.inl ⟨c, rfl, hx, ?_⟩)⟩
            simp only [cmS2, cmCopy, hre, ↓reduceIte, cmS1, hsge]
            rw [hlb]; exact hs0
          · cases h
        · by_cases hre : lb.clientProposals ≠ [] ∧ m.cmds = []
          · have hre' : cmRe c m := ⟨lb, hlb, hre⟩
            simp only [hlb, hre, ↓reduceIte, ne_eq, not_false_eq_true, and_self] at h
            split at h
            · rename_i s0 hs0
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨rfl, .inr (.inl ⟨c, rfl, hx, ?_⟩)⟩
              simp only [cmS2, cmCopy, hre', ↓reduceIte, cmS1, hsge, cmProps, hlb]
              simp only [hre.2] at hs0 ⊢; exact hs0
            · cases h
          · have hre' : ¬ cmRe c m := by
              rintro ⟨lb', h1, h2⟩; rw [hlb] at h1; cases h1; exact hre h2
            simp only [hlb, hre, ↓reduceIte] at h
            split at h
            · rename_i s0 hs0
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨rfl, .inr (.inl ⟨c, rfl, hx, ?_⟩)⟩
              simp only [cmS2, cmCopy, hre', ↓reduceIte, cmS1, hsge]
              rw [hlb]; exact hs0
            · cases h

end Perennial.gryff.replica2
