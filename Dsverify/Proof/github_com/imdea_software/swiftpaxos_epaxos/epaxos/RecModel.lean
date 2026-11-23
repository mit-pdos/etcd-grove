/-
Pure facts about the model's `hRecover` by branch.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ModelFacts

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

section
variable (σ : RState) (x : InstId)

theorem hRec_done (h : stGe (getOrDefault σ x).2.status stCOMMITTED ∧
    (getOrDefault σ x).2.cmds ≠ none) :
    hRecover σ x = ((getOrDefault σ x).1, []) := by
  simp [hRecover, h]

theorem hRec_ovf (h : ¬ (stGe (getOrDefault σ x).2.status stCOMMITTED ∧
    (getOrDefault σ x).2.cmds ≠ none))
    (ho : (2 ^ 31 - 1 : Int) < makeBallotZ (getOrDefault σ x).1 (getOrDefault σ x).2.bal (W32 0)) :
    hRecover σ x = ((getOrDefault σ x).1, []) := by
  unfold hRecover
  simp only [h, ho, if_false, if_true]

/-! ## The main branch, named -/

/-- The instance recovery finds (created if nil). -/
def recW0 (σ : RState) (x : InstId) : InstRec := (getOrDefault σ x).2

/-- The recovery ballot. -/
def recN (σ : RState) (x : InstId) : w32 := W32 (makeBallotZ σ (recW0 σ x).bal (W32 0))

/-- The replica's own PrepareReply. -/
def recReply (σ : RState) (x : InstId) : PrepareReply :=
  { acceptorId := W32 σ.id, replica := W32 x.q, inst := W32 x.i, ballot := recN σ x,
    vballot := (recW0 σ x).vbal, status := (recW0 σ x).status,
    command := (recW0 σ x).cmds.getD [], seq := (recW0 σ x).seq, deps := (recW0 σ x).deps }

/-- The new bookkeeping. -/
def recLb (σ : RState) (x : InstId) : LbRec :=
  { clientProposals := (recW0 σ x).lb.bind (·.clientProposals), ballot := (recW0 σ x).vbal,
    allEqual := true, preAcceptOKs := W64 0, acceptOKs := W64 0, nacks := W64 0,
    prepareReplies := [⟨recReply σ x, (recW0 σ x).cmds = none⟩], preparing := true,
    tryingToPreAccept := false, lastTriedBallot := recN σ x, cmds := (recW0 σ x).cmds,
    status := (recW0 σ x).status, seq := (recW0 σ x).seq, deps := (recW0 σ x).deps,
    leaderResponded := decide (σ.id = x.q), preAcceptsSent := W64 0 }

/-- The recovered instance. -/
def recInst (σ : RState) (x : InstId) : InstRec :=
  { recW0 σ x with lb := some (recLb σ x), bal := recN σ x }

/-- The final state. -/
def recSt (σ : RState) (x : InstId) : RState := σ.setInst x (recInst σ x)

theorem makeBallotZ_god (b lt : w32) :
    makeBallotZ (getOrDefault σ x).1 b lt = makeBallotZ σ b lt := by
  unfold getOrDefault; split <;> rfl

theorem god_id : (getOrDefault σ x).1.id = σ.id := by
  unfold getOrDefault; split <;> rfl

theorem hRec_main (h : ¬ (stGe (recW0 σ x).status stCOMMITTED ∧ (recW0 σ x).cmds ≠ none))
    (ho : ¬ (2 ^ 31 - 1 : Int) < makeBallotZ σ (recW0 σ x).bal (W32 0)) :
    hRecover σ x = (recSt σ x,
      [Out.ev (.makeBallot x (recN σ x)), Out.ev (.selfReply (recReply σ x))] ++
      [Out.bcast (bcastPrepareOf (recSt σ x) x (recN σ x))]) := by
  have hs : (getOrDefault σ x).1.setInst x (recInst σ x) = recSt σ x := by
    unfold recSt getOrDefault RState.setInst
    split
    · rfl
    · simp only [upd_upd]
  unfold recW0 at h ho
  unfold hRecover
  simp only [h, if_false, makeBallotZ_god, ho]
  rw [← hs]
  simp only [recInst, recLb, recReply, recN, recW0, god_id, List.cons_append, List.nil_append]
  rfl

end

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
