/-
Pure facts about the model's `hAcceptReply` and `hPreAcceptReply` (`Epaxos/Model/State.lean`):
their results, branch by branch, for the heap proofs.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ModelFacts

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

/-! ## `hAcceptReply` -/

section
variable (σ : RState) (m : AcceptReply) (w : InstRec) (lb : LbRec)
variable (hw : σ.inst ⟨toN m.replica, toN m.inst⟩ = some w) (hlb : w.lb = some lb)
include hw hlb

theorem hAR_ret1 (h : (lb.status ≠ stACCEPTED ∨ stGe w.status stCOMMITTED = true)) :
    hAcceptReply σ m = (bumpRecvBallot σ m.ballot, []) := by
  simp [hAcceptReply, hw, hlb, h]

theorem hAR_ret2 (h : ¬ (lb.status ≠ stACCEPTED ∨ stGe w.status stCOMMITTED = true))
    (hb : lb.lastTriedBallot.slt w.bal = true) :
    hAcceptReply σ m = (bumpRecvBallot σ m.ballot, []) := by
  simp only [hAcceptReply, hw, hlb]
  rw [if_neg h]; simp [hb]

theorem hAR_ret3 (h : ¬ (lb.status ≠ stACCEPTED ∨ stGe w.status stCOMMITTED = true))
    (hb : lb.lastTriedBallot.slt w.bal = false) (hne : lb.lastTriedBallot ≠ m.ballot) :
    hAcceptReply σ m = (bumpRecvBallot σ m.ballot, []) := by
  simp only [hAcceptReply, hw, hlb]
  rw [if_neg h]; simp [hb, hne]

theorem hAR_few (h : ¬ (lb.status ≠ stACCEPTED ∨ stGe w.status stCOMMITTED = true))
    (hb : lb.lastTriedBallot.slt w.bal = false) (he : lb.lastTriedBallot = m.ballot)
    (hq : (W64 (nR / 2)).slt (lb.acceptOKs + 1 + 1) = false) :
    hAcceptReply σ m = ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
      { w with lb := some { lb with acceptOKs := lb.acceptOKs + 1 } }, []) := by
  simp only [hAcceptReply, hw, hlb]
  rw [if_neg h]
  rw [← he]
  have hns : lb.lastTriedBallot.slt lb.lastTriedBallot = false := by simp [BitVec.slt]
  simp [hb, hns]
  exact hq

/-- The commit (a majority of AcceptReplies). -/
def arLb (lb : LbRec) : LbRec := { lb with acceptOKs := lb.acceptOKs + 1, status := stCOMMITTED }
def arInst (w : InstRec) (lb : LbRec) : InstRec := { w with status := stCOMMITTED, lb := some (arLb lb) }

theorem hAR_commit (h : ¬ (lb.status ≠ stACCEPTED ∨ stGe w.status stCOMMITTED = true))
    (hb : lb.lastTriedBallot.slt w.bal = false) (he : lb.lastTriedBallot = m.ballot)
    (hq : (W64 (nR / 2)).slt (lb.acceptOKs + 1 + 1) = true) :
    hAcceptReply σ m =
      (updateCommitted ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
          (arInst w lb)) (toN m.replica),
        [Out.ev (.commit ⟨toN m.replica, toN m.inst⟩ w.bal (⟨w.cmds.getD [], w.seq, w.deps⟩ : Val)),
         Out.bcast (bcastCommitOf
          (updateCommitted ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
            (arInst w lb)) (toN m.replica)) ⟨toN m.replica, toN m.inst⟩
          (commitOf (updateCommitted ((bumpRecvBallot σ m.ballot).setInst
            ⟨toN m.replica, toN m.inst⟩ (arInst w lb)) (toN m.replica)) m.replica m.inst
            (arLb lb)))]) := by
  simp only [hAcceptReply, hw, hlb]
  rw [if_neg h]
  rw [← he]
  have hns : lb.lastTriedBallot.slt lb.lastTriedBallot = false := by simp [BitVec.slt]
  simp [hb, hns, arInst, arLb]
  exact hq

end

/-! ## `hPreAcceptReply` -/

def parLb1 (lb : LbRec) : LbRec := { lb with preAcceptOKs := lb.preAcceptOKs + 1 }
def parLb2 (lb : LbRec) (m : PreAcceptReply) : LbRec :=
  if (parLb1 lb).ballot.slt m.vballot then
    { (parLb1 lb) with ballot := m.vballot, seq := m.seq, deps := m.deps, status := m.status }
  else parLb1 lb
def parMg (lb : LbRec) (m : PreAcceptReply) : w32 × List w32 × Bool :=
  mergeAttributes (parLb2 lb m).seq (parLb2 lb m).deps m.seq m.deps
def parLb3 (lb : LbRec) (m : PreAcceptReply) : LbRec :=
  { (parLb2 lb m) with allEqual := (parLb2 lb m).allEqual && (parMg lb m).2.2 }
def parLb4 (lb : LbRec) (m : PreAcceptReply) : LbRec :=
  if (parLb3 lb m).status.sle stPREACCEPTED_EQ then
    { (parLb3 lb m) with deps := (parMg lb m).2.1, seq := (parMg lb m).1 }
  else parLb3 lb m
def parPre (lb : LbRec) (m : PreAcceptReply) : Bool :=
  (parLb4 lb m).allEqual && isInitialBallot (parLb2 lb m).lastTriedBallot m.replica
def parSlow (lb : LbRec) (m : PreAcceptReply) : Bool :=
  (W64 (nR / 2)).sle (parLb4 lb m).preAcceptOKs &&
    Bool.or (!parPre lb m) ((parLb4 lb m).preAcceptsSent.sle (parLb4 lb m).preAcceptOKs)
def parFast (lb : LbRec) (m : PreAcceptReply) : Bool :=
  (W64 (2 * fR - 1)).sle (parLb4 lb m).preAcceptOKs && parPre lb m
def parLbF (lb : LbRec) (m : PreAcceptReply) : LbRec := { (parLb4 lb m) with status := stCOMMITTED }
def parInstF (w : InstRec) (lb : LbRec) (m : PreAcceptReply) : InstRec :=
  { w with status := stCOMMITTED, bal := (parLbF lb m).ballot, cmds := (parLbF lb m).cmds,
           deps := (parLbF lb m).deps, seq := (parLbF lb m).seq, lb := some (parLbF lb m) }
def parLbS (lb : LbRec) (m : PreAcceptReply) : LbRec := { (parLb4 lb m) with status := stACCEPTED }
def parInstS (w : InstRec) (lb : LbRec) (m : PreAcceptReply) : InstRec :=
  { w with status := stACCEPTED, bal := (parLbS lb m).ballot, cmds := (parLbS lb m).cmds,
           deps := (parLbS lb m).deps, seq := (parLbS lb m).seq, lb := some (parLbS lb m) }

theorem parLb2_ltb (lb : LbRec) (m : PreAcceptReply) :
    (parLb2 lb m).lastTriedBallot = lb.lastTriedBallot := by unfold parLb2; split <;> rfl
theorem parLb4_ltb (lb : LbRec) (m : PreAcceptReply) :
    (parLb4 lb m).lastTriedBallot = lb.lastTriedBallot := by
  unfold parLb4 parLb3; split <;> simp [parLb2_ltb]

section
variable (σ : RState) (m : PreAcceptReply) (w : InstRec) (lb : LbRec)
variable (hw : σ.inst ⟨toN m.replica, toN m.inst⟩ = some w) (hlb : w.lb = some lb)
include hw hlb

theorem hPAR_ret1 (h : stGe w.status stCOMMITTED = true) :
    hPreAcceptReply σ m = (bumpRecvBallot σ m.ballot, []) := by
  simp [hPreAcceptReply, hw, hlb, h]

theorem hPAR_ret2 (h : stGe w.status stCOMMITTED = false)
    (hb : lb.lastTriedBallot.slt w.bal = true) :
    hPreAcceptReply σ m = (bumpRecvBallot σ m.ballot, []) := by
  simp [hPreAcceptReply, hw, hlb, h, hb]

theorem hPAR_ret3 (h : stGe w.status stCOMMITTED = false)
    (hb : lb.lastTriedBallot.slt w.bal = false) (hl : m.ballot.slt lb.lastTriedBallot = true) :
    hPreAcceptReply σ m = (bumpRecvBallot σ m.ballot, []) := by
  simp [hPreAcceptReply, hw, hlb, h, hb, hl]

theorem hPAR_ret4 (h : stGe w.status stCOMMITTED = false)
    (hb : lb.lastTriedBallot.slt w.bal = false) (hl : m.ballot.slt lb.lastTriedBallot = false)
    (hn : lb.lastTriedBallot.slt m.ballot = false)
    (hs : ¬ (lb.status = stPREACCEPTED ∨ lb.status = stPREACCEPTED_EQ)) :
    hPreAcceptReply σ m = (bumpRecvBallot σ m.ballot, []) := by
  simp only [hPreAcceptReply, hw, hlb, h, hb, hl, hn]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [if_pos hs]

set_option maxHeartbeats 4000000 in
theorem hPAR_main (h : stGe w.status stCOMMITTED = false)
    (hb : lb.lastTriedBallot.slt w.bal = false) (hl : m.ballot.slt lb.lastTriedBallot = false)
    (hn : lb.lastTriedBallot.slt m.ballot = false)
    (hs : lb.status = stPREACCEPTED ∨ lb.status = stPREACCEPTED_EQ) :
    hPreAcceptReply σ m =
      if parFast lb m then
        (updateCommitted ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
            (parInstF w lb m)) (toN m.replica),
          [Out.ev (.commit ⟨toN m.replica, toN m.inst⟩ (parLbF lb m).ballot (lbVal (parLbF lb m))),
           Out.ev (.fastCommit ⟨toN m.replica, toN m.inst⟩ (lbVal (parLbF lb m))),
           Out.bcast (bcastCommitOf
            (updateCommitted ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
              (parInstF w lb m)) (toN m.replica)) ⟨toN m.replica, toN m.inst⟩
            (commitOf (updateCommitted ((bumpRecvBallot σ m.ballot).setInst
              ⟨toN m.replica, toN m.inst⟩ (parInstF w lb m)) (toN m.replica))
              m.replica m.inst (parLbF lb m)))])
      else if parSlow lb m then
        ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩ (parInstS w lb m),
          [Out.ev (.vote ⟨toN m.replica, toN m.inst⟩ (parInstS w lb m).vbal stACCEPTED
              (lbVal (parLbS lb m))),
           Out.ev (.accept ⟨toN m.replica, toN m.inst⟩ (parLbS lb m).lastTriedBallot
              (lbVal (parLbS lb m))),
           Out.bcast (bcastAcceptOf
            ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩ (parInstS w lb m))
            ⟨toN m.replica, toN m.inst⟩
            (acceptOf ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
              (parInstS w lb m)) m.replica m.inst (parLbS lb m)))])
      else
        ((bumpRecvBallot σ m.ballot).setInst ⟨toN m.replica, toN m.inst⟩
          { w with lb := some (parLb4 lb m) }, []) := by
  simp only [hPreAcceptReply, hw, hlb]
  rw [if_neg (by simp [h]), if_neg (by simp [hb]), if_neg (by simp [hl]), if_neg (by simp [hn]),
    if_neg (fun h' => h' hs)]
  rfl

end

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
