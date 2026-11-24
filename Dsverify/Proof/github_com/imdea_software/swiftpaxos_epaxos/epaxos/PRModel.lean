/-
Pure facts about the model's `hPrepareReply` (`Epaxos/Model/State.lean`): its result, branch by
branch, for `handlePrepareReply`'s heap proof.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ModelFacts

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

/-- The replies after `m` is recorded. -/
def prReps (lb : LbRec) (m : PrepareReply) : List PReply := lb.prepareReplies ++ [⟨m, false⟩]

/-- `lb.leaderResponded` after the first loop. -/
def prLr (lb : LbRec) (m : PrepareReply) : Bool :=
  Bool.or lb.leaderResponded <| (prReps lb m).any (fun e => e.m.acceptorId == e.m.replica)

/-- `maxVbal` after the first loop. -/
def prMax (lb : LbRec) (m : PrepareReply) : w32 :=
  (prReps lb m).foldl (fun mx e => if mx.slt e.m.vballot then e.m.vballot else mx) (W32 (-1))

/-- The decision. -/
def prDec (lb : LbRec) (m : PrepareReply) : Nat × Option PReply :=
  prepDecide (prReps lb m) (prMax lb m) (prLr lb m) m.replica

/-- The bookkeeping after the decision's assignments. -/
def prLb (lb : LbRec) (m : PrepareReply) : LbRec :=
  let lb1 := { lb with prepareReplies := prReps lb m, preparing := false,
                       leaderResponded := prLr lb m, ballot := prMax lb m }
  match (prDec lb m).2 with
  | some e => { lb1 with cmds := if e.cmdsNil then none else some e.m.command,
                         seq := e.m.seq, deps := e.m.deps, status := e.m.status }
  | none => { lb1 with cmds := some noop, status := stNONE }

/-- The instance after the decision's assignments. -/
def prInst (w : InstRec) (lb : LbRec) (m : PrepareReply) : InstRec :=
  { w with cmds := (prLb lb m).cmds, bal := (prLb lb m).lastTriedBallot,
           vbal := (prLb lb m).lastTriedBallot,
           seq := (prLb lb m).seq, deps := (prLb lb m).deps, status := (prLb lb m).status }

/-- The committed instance (sub-case 1). -/
def prInstC (w : InstRec) (lb : LbRec) (m : PrepareReply) : InstRec :=
  { (prInst w lb m) with status := stCOMMITTED, lb := some { (prLb lb m) with status := stCOMMITTED } }

/-- The bookkeeping of sub-cases 2/3. -/
def prLbA (lb : LbRec) (m : PrepareReply) : LbRec := { (prLb lb m) with status := stACCEPTED }

/-- The accepted instance (sub-cases 2/3). -/
def prInstA (w : InstRec) (lb : LbRec) (m : PrepareReply) : InstRec :=
  { (prInst w lb m) with status := stACCEPTED, lb := some (prLbA lb m) }

/-- The instance before `startPhase1` (sub-cases 5/6). -/
def prInstP (w : InstRec) (lb : LbRec) (m : PrepareReply) : InstRec :=
  { (prInst w lb m) with lb := some (prLb lb m) }

theorem prLb_ltb (lb : LbRec) (m : PrepareReply) :
    (prLb lb m).lastTriedBallot = lb.lastTriedBallot := by unfold prLb; split <;> rfl

theorem prLb_cp (lb : LbRec) (m : PrepareReply) :
    (prLb lb m).clientProposals = lb.clientProposals := by unfold prLb; split <;> rfl

section
variable (σ : RState) (m : PrepareReply) (w : InstRec) (lb : LbRec)
variable (hw : σ.inst ⟨toN m.replica, toN m.inst⟩ = some w) (hlb : w.lb = some lb)
include hw hlb

theorem hPR_notPrep (h : lb.preparing = false) :
    hPrepareReply σ m = (bumpRecvBallot σ m.ballot, []) := by
  simp [hPrepareReply, hw, hlb, h]

theorem hPR_committed (h : lb.preparing = true) (hc : stGe w.status stCOMMITTED = true) :
    hPrepareReply σ m = ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
      { w with lb := some { lb with preparing := false } }, []) := by
  simp [hPrepareReply, hw, hlb, h, hc]

theorem hPR_promised (h : lb.preparing = true) (hc : stGe w.status stCOMMITTED = false)
    (hb : lb.lastTriedBallot.slt w.bal = true) :
    hPrepareReply σ m = ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
      { w with lb := some { lb with preparing := false } }, []) := by
  simp [hPrepareReply, hw, hlb, h, hc, hb]

theorem hPR_nack (h : lb.preparing = true) (hc : stGe w.status stCOMMITTED = false)
    (hb : lb.lastTriedBallot.slt w.bal = false) (hne : m.ballot ≠ lb.lastTriedBallot) :
    hPrepareReply σ m = ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
      { w with lb := some { lb with nacks := lb.nacks + 1 } }, []) := by
  simp [hPrepareReply, hw, hlb, h, hc, hb, hne]

theorem hPR_dup (h : lb.preparing = true) (hc : stGe w.status stCOMMITTED = false)
    (hb : lb.lastTriedBallot.slt w.bal = false) (he : m.ballot = lb.lastTriedBallot)
    (hd : lb.prepareReplies.any (fun e => e.m.acceptorId == m.acceptorId) = true) :
    hPrepareReply σ m = (bumpRecvBallot σ m.ballot, []) := by
  simp only [hPrepareReply, hw, hlb, h, hc, hb, he]
  simp [hd]

theorem hPR_few (h : lb.preparing = true) (hc : stGe w.status stCOMMITTED = false)
    (hb : lb.lastTriedBallot.slt w.bal = false) (he : m.ballot = lb.lastTriedBallot)
    (hd : lb.prepareReplies.any (fun e => e.m.acceptorId == m.acceptorId) = false)
    (hl : (prReps lb m).length < (nR + 1) / 2) :
    hPrepareReply σ m = ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
      { w with lb := some { lb with prepareReplies := prReps lb m } }, []) := by
  unfold prReps at hl
  simp only [hPrepareReply, hw, hlb, h, hc, hb, he, hd]
  simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  rw [if_pos hl]
  rfl

/-- The decision taken: the state and outputs by sub-case. -/
theorem hPR_main (h : lb.preparing = true) (hc : stGe w.status stCOMMITTED = false)
    (hb : lb.lastTriedBallot.slt w.bal = false) (he : m.ballot = lb.lastTriedBallot)
    (hd : lb.prepareReplies.any (fun e => e.m.acceptorId == m.acceptorId) = false)
    (hl : ¬ (prReps lb m).length < (nR + 1) / 2) :
    hPrepareReply σ m =
      if (prDec lb m).1 = 1 then
        (updateCommitted ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
            (prInstC w lb m)) (toN m.replica),
          [Out.ev (.commit ⟨toN m.replica, toN m.inst⟩ (prInstC w lb m).bal
            ⟨(prInstC w lb m).cmds.getD [], (prInstC w lb m).seq, (prInstC w lb m).deps⟩)])
      else if (prDec lb m).1 = 2 ∨ (prDec lb m).1 = 3 then
        ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩ (prInstA w lb m),
          [Out.ev (.vote ⟨toN m.replica, toN m.inst⟩ (prLbA lb m).lastTriedBallot stACCEPTED
              (lbVal (prLbA lb m))),
            Out.ev (.accept ⟨toN m.replica, toN m.inst⟩ (prLbA lb m).lastTriedBallot
              (lbVal (prLbA lb m))),
            Out.bcast (bcastAcceptOf
              ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩ (prInstA w lb m))
              ⟨toN m.replica, toN m.inst⟩
              (acceptOf ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
                (prInstA w lb m)) m.replica m.inst (prLbA lb m)))])
      else
        startPhase1 ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
            (prInstP w lb m))
          ((prLb lb m).cmds.getD []) ⟨toN m.replica, toN m.inst⟩ m.replica m.inst
          (prLb lb m).lastTriedBallot (prLb lb m).clientProposals := by
  unfold prReps at hl
  simp only [hPrepareReply, hw, hlb, h, hc, hb, he, hd]
  simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  rw [if_neg hl]
  simp only [prDec, prReps, prMax, prLr, prLb, prInst, prInstC, prInstA, prLbA, prInstP,
    Bool.true_eq_false, ↓reduceIte]
  refine ite_congr rfl (fun _ => ?_) (fun _ => ite_congr rfl (fun _ => ?_) (fun _ => ?_))
  · rfl
  · rfl
  · rfl

end

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
