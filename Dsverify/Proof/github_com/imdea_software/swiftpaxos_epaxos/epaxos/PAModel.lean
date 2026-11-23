/-
The model's `hPreAccept`, named branch by branch (for `wp_handlePreAccept`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ModelFacts

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

section
variable (σ : RState) (m : PreAccept)

/-- `maxSeq` after `if preAccept.Seq >= r.maxSeq`. -/
def paMs : w32 := if σ.maxSeq.sle m.seq then m.seq + 1 else σ.maxSeq

/-- The instance found (created if nil). -/
def paW0 : InstRec := (getOrDefault σ ⟨toN m.replica, toN m.inst⟩).2

/-- The state after the first statements (`maxSeq`, `maxRecvBallot`, `crtInstance`, the
instance). -/
def paPre : RState :=
  { σ with maxSeq := paMs σ m,
           crtInstance := (bumpCrt σ (toN m.replica) m.inst).crtInstance,
           maxRecvBallot := (bumpRecvBallot σ m.ballot).maxRecvBallot,
           inst := upd σ.inst ⟨toN m.replica, toN m.inst⟩ (some (paW0 σ m)) }

/-- `updateAttributes` in the pre-accept path. -/
def paAttrs : w32 × List w32 × Bool := updateAttributes (paPre σ m) m.command m.seq m.deps

/-- Whether the instance is ACCEPTED or later. -/
def paAcc : Bool := stGe (paW0 σ m).status stACCEPTED

/-- The final instance. -/
def paW2 : InstRec :=
  if paAcc σ m = true then
    if (paW0 σ m).cmds = none then { paW0 σ m with bal := m.ballot, cmds := some m.command }
    else { paW0 σ m with bal := m.ballot }
  else
    { paW0 σ m with
      cmds := some m.command
      seq := (paAttrs σ m).1
      deps := (paAttrs σ m).2.1
      bal := m.ballot
      vbal := m.ballot
      status := if (paAttrs σ m).2.2 then stPREACCEPTED else stPREACCEPTED_EQ }

/-- The final state. -/
def paFin : RState :=
  if paAcc σ m = true ∧ (paW0 σ m).cmds ≠ none then
    (paPre σ m).setInst ⟨toN m.replica, toN m.inst⟩ (paW2 σ m)
  else updateConflicts ((paPre σ m).setInst ⟨toN m.replica, toN m.inst⟩ (paW2 σ m)) m.command
    (toN m.replica) m.inst m.seq

/-- The events. -/
def paEvs : List Out :=
  if paAcc σ m = true then
    if (paW0 σ m).cmds = none then [Out.ev (.record ⟨toN m.replica, toN m.inst⟩ m.command)]
    else []
  else
    [Out.ev (.vote ⟨toN m.replica, toN m.inst⟩ m.ballot (paW2 σ m).status
        ⟨m.command, (paAttrs σ m).1, (paAttrs σ m).2.1⟩),
     Out.ev (.attrsRec ⟨toN m.replica, toN m.inst⟩ m.command (paAttrs σ m).2.1)]

/-- The reply. -/
def paReply : PreAcceptReply :=
  { replica := m.replica, inst := m.inst, ballot := (paW2 σ m).bal, vballot := (paW2 σ m).vbal,
    seq := (paW2 σ m).seq, deps := (paW2 σ m).deps, committedDeps := (paFin σ m).committedList,
    status := (paW2 σ m).status }

theorem hPA_pre :
    getOrDefault (bumpCrt (bumpRecvBallot
      (if σ.maxSeq.sle m.seq then { σ with maxSeq := m.seq + 1 } else σ) m.ballot)
      (toN m.replica) m.inst) ⟨toN m.replica, toN m.inst⟩ = (paPre σ m, paW0 σ m) := by
  have e : (getOrDefault (bumpCrt (bumpRecvBallot
      (if σ.maxSeq.sle m.seq then { σ with maxSeq := m.seq + 1 } else σ) m.ballot)
      (toN m.replica) m.inst) ⟨toN m.replica, toN m.inst⟩).2 =
      (getOrDefault σ ⟨toN m.replica, toN m.inst⟩).2 := by
    apply getOrDefault_snd_inst
    unfold bumpRecvBallot bumpCrt; split <;> split <;> split <;> rfl
  apply Prod.ext
  · rw [getOrDefault_fst, e]
    unfold paPre paW0 paMs bumpRecvBallot bumpCrt
    split <;> split <;> split <;> simp_all
  · exact e

theorem hPreAccept_eq :
    hPreAccept σ m =
      if m.ballot.slt (paW0 σ m).bal then (paPre σ m, [])
      else (paFin σ m, paEvs σ m ++
        [Out.send (toN m.leaderId) (.preAcceptReply (paReply σ m))]) := by
  unfold hPreAccept
  simp only
  rw [hPA_pre]
  simp only
  split
  · rfl
  · unfold paFin paEvs paReply paW2 paAttrs paAcc
    split
    · split <;> simp_all [paFin, paW2, paAcc]
    · simp_all [paFin, paW2, paAcc, paAttrs] <;> rfl

/-- The conflicts after the handler. -/
def paCf : Nat → w64 → Option InstPair :=
  if paAcc σ m = true ∧ (paW0 σ m).cmds ≠ none then σ.conflicts
  else (updateConflicts σ m.command (toN m.replica) m.inst m.seq).conflicts

/-- `maxSeqPerKey` after the handler. -/
def paMk : w64 → Option w32 :=
  if paAcc σ m = true ∧ (paW0 σ m).cmds ≠ none then σ.maxSeqPerKey
  else (updateConflicts σ m.command (toN m.replica) m.inst m.seq).maxSeqPerKey

/-- `lastScan` after the handler. -/
def paLS : Nat → w32 :=
  if paAcc σ m = true ∧ (paW0 σ m).cmds ≠ none then σ.lastScan
  else (updateConflicts σ m.command (toN m.replica) m.inst m.seq).lastScan

/-- `lastPut` after the handler. -/
def paLP : Nat → w32 :=
  if paAcc σ m = true ∧ (paW0 σ m).cmds ≠ none then σ.lastPut
  else (updateConflicts σ m.command (toN m.replica) m.inst m.seq).lastPut

theorem paFin_eq :
    paFin σ m = { σ with maxSeq := paMs σ m,
                         crtInstance := (bumpCrt σ (toN m.replica) m.inst).crtInstance,
                         maxRecvBallot := (bumpRecvBallot σ m.ballot).maxRecvBallot,
                         inst := upd σ.inst ⟨toN m.replica, toN m.inst⟩ (some (paW2 σ m)),
                         conflicts := paCf σ m, maxSeqPerKey := paMk σ m,
                         lastScan := paLS σ m, lastPut := paLP σ m } := by
  unfold paFin paCf paMk paLS paLP
  split
  · rename_i h
    simp only [h, and_self, ne_eq, not_false_eq_true, ite_true, paPre, RState.setInst, upd_upd]
  · rename_i h
    rw [updateConflicts_eq]
    have hm := updateConflicts_maps ((paPre σ m).setInst ⟨toN m.replica, toN m.inst⟩ (paW2 σ m))
      σ m.command (toN m.replica) m.inst m.seq rfl rfl
    have hl := updateConflicts_cls ((paPre σ m).setInst ⟨toN m.replica, toN m.inst⟩ (paW2 σ m))
      σ m.command (toN m.replica) m.inst m.seq rfl rfl
    rw [hm.1, hm.2, hl.1, hl.2]
    simp only [h, if_false, paPre, RState.setInst, upd_upd]

end

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
