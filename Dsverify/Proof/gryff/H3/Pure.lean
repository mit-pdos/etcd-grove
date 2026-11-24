/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H3/Pure.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H3: the recovery steps' results, cut along the Go code's control flow (pure).
`stepPrepareReply` is split into the phases the code runs one after the other: the guards, the
committed reply, the candidate's updates (`prAcc`: an ACCEPTED reply; `prPre`: a pre-accepted
one), the quorum test and the choice (`prChoose`).
-/
module

public import Dsverify.Proof.gryff.Model.Step

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2.h3

open Perennial.gryff.model

/-- An ACCEPTED reply beats the candidate (none, not ACCEPTED, or of a smaller `vbal`). -/
def prBetter (lb : LB) (m : PrepareReplyM) : Bool :=
  match lb.recoveryInst with
  | none => true
  | some ri => decide (ri.status ≠ St.ACCEPTED) || slt ri.vbal m.vbal

/-- The candidate after an ACCEPTED reply (the code's first `if preply.Status == ACCEPTED`). -/
def prAcc (lb : LB) (m : PrepareReplyM) : LB :=
  if m.status = St.ACCEPTED then
    if prBetter lb m then { lb with recoveryInst := some (riOf m 0 false) } else lb
  else lb

/-- The reply is pre-accepted and the candidate is below ACCEPTED (the code's second `if`). -/
def prPreCond (lb : LB) (m : PrepareReplyM) : Prop :=
  (m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) ∧
    (match lb.recoveryInst with | none => true | some ri => slt ri.status St.ACCEPTED) = true

instance (lb : LB) (m : PrepareReplyM) : Decidable (prPreCond lb m) := by
  unfold prPreCond; infer_instance

/-- The reply is a copy unchanged from the leader's initial PreAccept. -/
abbrev prUnchanged (m : PrepareReplyM) : Bool :=
  m.status == St.PREACCEPTED_EQ && m.vbal == 0 && m.acceptorId != m.replica

/-- The candidate after a pre-accepted reply (inside the second `if`, before `leaderResponded`). -/
def prPre (lb : LB) (m : PrepareReplyM) : LB :=
  match lb.recoveryInst with
  | none => { lb with recoveryInst := some (riOf m (if prUnchanged m then 1 else 0) false) }
  | some ri =>
    if prUnchanged m && sgt ri.preAcceptCount 0 then
      { lb with recoveryInst := some { ri with preAcceptCount := ri.preAcceptCount + 1 } }
    else if prUnchanged m then
      { lb with recoveryInst := some (riOf m 1 ri.leaderResponded) }
    else lb

/-- The candidate marked as having heard from the instance's leader. -/
def prLeader (lb : LB) : LB :=
  match lb.recoveryInst with
  | none => lb
  | some ri => { lb with recoveryInst := some { ri with leaderResponded := true } }

/-- The choice once a majority replied (`lb` the bookkeeping, `c` the copy): the model's text. -/
def prChoose (s : RState) (m : PrepareReplyM) (c : Copy) (lb : LB) : StepRes := do
  match lb.recoveryInst with
  | some ir =>
    if ir.status = St.ACCEPTED ∨
        (!ir.leaderResponded ∧ sge ir.preAcceptCount NHALF ∧ ir.status = St.PREACCEPTED_EQ) then
      let c' := { c with cmds := ir.cmds, seq := ir.seq, deps := ir.deps, base := ir.base,
                         status := St.ACCEPTED, vbal := c.ballot,
                         lb := some { lb with preparing := false } }
      let s := s.setInst m.replica m.inst c'
      let some outs := bcastAccept s m.replica m.inst c'.ballot c'.cmds c'.seq c'.deps c'.base
        | dead
      return (s, outs)
    else if !ir.leaderResponded ∧ sge ir.preAcceptCount ((NHALF + 1) / 2) then
      dead
    else
      let s := s.setInst m.replica m.inst { c with lb := some { lb with preparing := false } }
      startPhase1 s m.replica m.inst c.ballot lb.clientProposals ir.cmds
  | none =>
    let noopDeps := nildeps.setAt m.replica.toNat (m.inst - 1)
    let c' : Copy :=
      { cmds := [], ballot := c.ballot, status := St.ACCEPTED, seq := 0, deps := noopDeps,
        base := vt0, lb := some { lb with preparing := false }, slot := m.inst,
        leader := m.replica, vbal := c.ballot }
    let s := s.setInst m.replica m.inst c'
    let some outs := bcastAccept s m.replica m.inst c.ballot [] 0 noopDeps vt0 | dead
    return (s, outs)

/-- The code from the quorum test on (the model's text). -/
def prQuorum (s : RState) (m : PrepareReplyM) (c : Copy) (lb : LB) : StepRes := do
  if slt lb.prepareOKs NHALF then
    return (s.setInst m.replica m.inst { c with lb := some lb }, [])
  prChoose s m c lb

/-- The code from the pre-accepted reply's test on (the model's text, `lb` after `prAcc`). -/
def prStage2 (s : RState) (m : PrepareReplyM) (c : Copy) (lb0 : LB) : StepRes := do
  let mut lb := lb0
  let below : Bool := match lb.recoveryInst with
    | none => true
    | some ri => slt ri.status St.ACCEPTED
  if (m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) ∧ below then
    let unchanged : Bool := m.status == St.PREACCEPTED_EQ && m.vbal == 0 && m.acceptorId != m.replica
    let count : w64 := if unchanged then 1 else 0
    match lb.recoveryInst with
    | none => lb := { lb with recoveryInst := some (riOf m count false) }
    | some ri =>
      if unchanged && sgt ri.preAcceptCount 0 then
        lb := { lb with recoveryInst := some { ri with preAcceptCount := ri.preAcceptCount + 1 } }
      else if unchanged then
        lb := { lb with recoveryInst := some (riOf m 1 ri.leaderResponded) }
    if m.acceptorId = m.replica then
      let some ri := lb.recoveryInst | dead
      lb := { lb with recoveryInst := some { ri with leaderResponded := true } }
      return (s.setInst m.replica m.inst { c with lb := some lb }, [])
  if slt lb.prepareOKs NHALF then
    return (s.setInst m.replica m.inst { c with lb := some lb }, [])
  prChoose s m c lb

/-- The code after the guards (the model's text). -/
def prMain (s : RState) (m : PrepareReplyM) (c : Copy) (lb0 : LB) : StepRes := do
  let mut lb := { lb0 with prepareOKs := lb0.prepareOKs + 1, preparing := true }
  if m.status = St.COMMITTED ∨ m.status = St.EXECUTED then
    let s := s.setInst m.replica m.inst
      { cmds := m.cmds, ballot := c.ballot, status := St.COMMITTED, seq := m.seq, deps := m.deps,
        base := m.base, lb := none, slot := m.inst, leader := m.replica, vbal := c.ballot }
    let some outs := bcastCommit s m.replica m.inst m.cmds m.seq m.deps m.base | dead
    return (s, outs)
  if m.status = St.ACCEPTED then
    if prBetter lb m then
      lb := { lb with recoveryInst := some (riOf m 0 false) }
  prStage2 s m c lb

theorem stepPrepareReply_main (s : RState) (m : PrepareReplyM) (c : Copy) (lb0 : LB)
    (hcmds : cmdsOk m.cmds = true) (hbox : inBox m.replica m.inst = true)
    (hc : s.inst m.replica m.inst = some c) (hlb : c.lb = some lb0) (hprep : lb0.preparing = true)
    (hnc : ¬(c.status = St.COMMITTED ∨ c.status = St.EXECUTED)) (hok : m.ok ≠ FALSE)
    (hbal : m.ballot = c.ballot) :
    stepPrepareReply s m = prMain s m c lb0 := by
  unfold stepPrepareReply
  simp (config := {zeta := false}) only [hcmds, hbox, hc, hlb, hprep, hnc, hok, hbal, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  rfl

/-- A committed reply: the copy is replaced by the reply's, committed, and broadcast. -/
theorem prMain_committed (s : RState) (m : PrepareReplyM) (c : Copy) (lb0 : LB)
    (h : m.status = St.COMMITTED ∨ m.status = St.EXECUTED) :
    prMain s m c lb0 =
      let s' := s.setInst m.replica m.inst
        { cmds := m.cmds, ballot := c.ballot, status := St.COMMITTED, seq := m.seq, deps := m.deps,
          base := m.base, lb := none, slot := m.inst, leader := m.replica, vbal := c.ballot }
      match bcastCommit s' m.replica m.inst m.cmds m.seq m.deps m.base with
      | some outs => pure (s', outs)
      | none => dead := by
  unfold prMain
  simp only [h, ↓reduceIte]
  split
  · next outs heq => rw [heq]
  · next x hx => cases hb : bcastCommit _ m.replica m.inst m.cmds m.seq m.deps m.base <;> simp_all <;> rfl

/-- A reply that is not committed: the ACCEPTED update, then the rest. -/
theorem prMain_open (s : RState) (m : PrepareReplyM) (c : Copy) (lb0 : LB)
    (h : ¬(m.status = St.COMMITTED ∨ m.status = St.EXECUTED)) :
    prMain s m c lb0 =
      prStage2 s m c (prAcc { lb0 with prepareOKs := lb0.prepareOKs + 1, preparing := true } m) := by
  unfold prMain prAcc
  simp (config := {zeta := false}) only [h, ↓reduceIte]
  by_cases hA : m.status = St.ACCEPTED
  · by_cases hb : prBetter { lb0 with prepareOKs := lb0.prepareOKs + 1, preparing := true } m = true
    · simp only [hA, hb, ↓reduceIte]
    · simp only [hA, hb, ↓reduceIte, Bool.false_eq_true]
  · simp only [hA, ↓reduceIte]

/-- The pre-accepted reply's update, the leader's reply, the quorum test. -/
theorem prStage2_eq (s : RState) (m : PrepareReplyM) (c : Copy) (lb : LB) :
    prStage2 s m c lb =
      if prPreCond lb m then
        if m.acceptorId = m.replica then
          pure (s.setInst m.replica m.inst { c with lb := some (prLeader (prPre lb m)) }, [])
        else prQuorum s m c (prPre lb m)
      else prQuorum s m c lb := by
  unfold prStage2 prQuorum prPreCond prPre prLeader
  obtain ⟨cp, mrb, po, ae, pao, ao, n, od, cd, ri0, pr, nre, rc⟩ := lb
  rcases ri0 with _ | ri
  · by_cases hP : m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ <;>
    by_cases hL : m.acceptorId = m.replica <;> simp [hP, hL]
  · by_cases hP : (m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ) ∧ slt ri.status St.ACCEPTED = true <;>
    by_cases hL : m.acceptorId = m.replica <;>
    by_cases hu : prUnchanged m = true <;> by_cases hc : sgt ri.preAcceptCount 0 = true <;>
    simp_all <;> (split <;> simp_all)

end Perennial.gryff.replica2.h3

namespace Perennial.gryff.replica2.h3
open Perennial.gryff.model

/-- A broadcast from replica `k`: to `k + 1`, then `k + 2` (mod 3). -/
theorem bcast_eq (s : RState) (k : Fin 3) (hid : s.id = BitVec.ofNat 32 k.val) (m : Msg) :
    bcast s m = some [.send (k + 1) m, .send (k + 2) m] := by
  have h0 : sint.Z (0 : w32) = 0 := rfl
  have h1 : sint.Z (1 : w32) = 1 := rfl
  have h2 : sint.Z (2 : w32) = 2 := rfl
  set_option linter.unusedSimpArgs false in
  rcases k with ⟨_ | _ | _ | n, hk⟩
  all_goals first | omega | (simp [bcast, peerOrder, sendPeer, sendTo, dstOf, hid, h0, h1, h2] <;> rfl)

end Perennial.gryff.replica2.h3

namespace Perennial.gryff.replica2.h3
open Perennial.gryff.model

/-- `handlePrepare`'s reply to a Prepare on a new copy. -/
def prepNewReply (s : RState) (m : PrepareM) : PrepareReplyM :=
  { acceptorId := s.id, replica := m.replica, inst := m.inst, ok := TRUE, ballot := m.ballot,
    vbal := -1, status := St.NONE, cmds := [], seq := -1, deps := nildeps, base := vt0 }

/-- `handlePrepare`'s new copy. -/
def prepNewCopy (m : PrepareM) : Copy :=
  { cmds := [], ballot := m.ballot, status := St.NONE, seq := 0, deps := nildeps, base := vt0,
    lb := none, slot := m.inst, leader := m.replica, vbal := -1 }

/-- `handlePrepare`'s copy after a Prepare (promised if the ballot is not smaller). -/
def prepCopy (m : PrepareM) (c : Copy) : Copy :=
  if slt m.ballot c.ballot then c else { c with ballot := m.ballot }

/-- `handlePrepare`'s reply on an existing copy (after `prepCopy`). -/
def prepReply (s : RState) (m : PrepareM) (c : Copy) : PrepareReplyM :=
  { acceptorId := s.id, replica := m.replica, inst := m.inst,
    ok := if slt m.ballot c.ballot then FALSE else TRUE, ballot := (prepCopy m c).ballot,
    vbal := c.vbal, status := c.status, cmds := c.cmds, seq := c.seq, deps := c.deps,
    base := c.base }

theorem stepPrepare_ok (s s' : RState) (m : PrepareM) (outs : List Out)
    (h : stepPrepare s m = .ok (s', outs)) :
    inBox m.replica m.inst = true ∧
    match s.inst m.replica m.inst with
    | none => ∃ o, sendPeer s m.leaderId (.prepareReply (prepNewReply s m)) = some o ∧
        s' = s.setInst m.replica m.inst (prepNewCopy m) ∧ outs = [o]
    | some c => ∃ o, sendPeer s m.leaderId (.prepareReply (prepReply s m c)) = some o ∧
        s' = s.setInst m.replica m.inst (prepCopy m c) ∧ outs = [o] := by
  unfold stepPrepare at h
  by_cases hb : inBox m.replica m.inst = true
  · refine ⟨hb, ?_⟩
    simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    rcases hc : s.inst m.replica m.inst with _ | c
    · simp only [hc] at h
      split at h
      · next o ho =>
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨o, ho, h.1.symm, h.2.symm⟩
      · cases h
    · simp only [hc] at h
      by_cases hlt : slt m.ballot c.ballot = true
      · simp only [hlt, ↓reduceIte] at h
        split at h
        · next o ho =>
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          refine ⟨o, ?_, ?_, h.2.symm⟩
          · simp only [prepReply, prepCopy, hlt, ↓reduceIte, Bool.false_eq_true]; exact ho
          · rw [← h.1]; simp [prepCopy, hlt]
        · cases h
      · simp only [hlt, ↓reduceIte, Bool.false_eq_true] at h
        split at h
        · next o ho =>
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          refine ⟨o, ?_, ?_, h.2.symm⟩
          · simp only [prepReply, prepCopy, hlt, ↓reduceIte, Bool.false_eq_true]; exact ho
          · rw [← h.1]; simp [prepCopy, hlt]
        · cases h
  · simp only [hb, Bool.not_false, ↓reduceIte] at h; cases h

end Perennial.gryff.replica2.h3

namespace Perennial.gryff.replica2.h3
open Perennial.gryff.model

/-- A send to a peer: its destination is a replica id other than the sender's. -/
theorem sendPeer_some (s : RState) (k : Fin 3) (hid : s.id = BitVec.ofNat 32 k.val) (x : w32)
    (m : Msg) (o : Out) (h : sendPeer s x m = some o) :
    ∃ q : Fin 3, x = BitVec.ofNat 32 q.val ∧ q ≠ k ∧ o = .send q m := by
  unfold sendPeer sendTo dstOf at h
  by_cases hx : x = s.id
  · simp [hx] at h
  · simp only [hx, ↓reduceIte] at h
    by_cases hr : 0 ≤ sint.Z x ∧ sint.Z x < 3
    · rw [dif_pos hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have hx' : x = BitVec.ofNat 32 (sint.Z x).toNat := by
        have hc := BitVec.toInt_eq_toNat_cond x
        have hlt := x.isLt
        simp only [sint.Z] at hr ⊢
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat]
        split at hc <;> omega
      refine ⟨⟨(sint.Z x).toNat, by omega⟩, hx', ?_, h.symm⟩
      intro e; apply hx; rw [hid, hx', ← e]
    · simp [hr] at h

end Perennial.gryff.replica2.h3

namespace Perennial.gryff.replica2.h3
open Perennial.gryff.model

/-! `setInst` changes the instances only. -/
section setInst
variable (s : RState) (q i : w32) (c : Copy)
theorem setInst_crtInstance : (s.setInst q i c).crtInstance = s.crtInstance := rfl
theorem setInst_crt (x : w32) : (s.setInst q i c).crt x = s.crt x := rfl
theorem setInst_confAt (x : Nat) : (s.setInst q i c).confAt x = s.confAt x := rfl
theorem setInst_maxSeqK0 : (s.setInst q i c).maxSeqK0 = s.maxSeqK0 := rfl
theorem setInst_committedUpTo : (s.setInst q i c).committedUpTo = s.committedUpTo := rfl
theorem setInst_prevValTag : (s.setInst q i c).prevValTag = s.prevValTag := rfl
theorem setInst_tag : (s.setInst q i c).tag = s.tag := rfl
theorem setInst_ongoing : (s.setInst q i c).ongoing = s.ongoing := rfl
theorem setInst_val : (s.setInst q i c).val = s.val := rfl
theorem setInst_proposeQ : (s.setInst q i c).proposeQ = s.proposeQ := rfl
theorem setInst_id : (s.setInst q i c).id = s.id := rfl
theorem setInst_maxN : (s.setInst q i c).maxN = s.maxN := rfl
theorem setInst_rops : (s.setInst q i c).rops = s.rops := rfl
theorem setInst_wops : (s.setInst q i c).wops = s.wops := rfl
theorem setInst_ongoingReqs : (s.setInst q i c).ongoingReqs = s.ongoingReqs := rfl
end setInst

end Perennial.gryff.replica2.h3

namespace Perennial.gryff.replica2.h3
open Perennial.gryff.model

/-- The copy recovery starts from (`InstanceSpace[q][i]`, or the fresh `&Instance{...}`). -/
def recBase (s : RState) (q i : w32) : Copy :=
  match s.inst q i with
  | some c => c
  | none => { cmds := [], ballot := 0, status := St.NONE, seq := 0, deps := nildeps, base := vt0,
              lb := none, slot := i, leader := q, vbal := -1 }

/-- The recovery's bookkeeping (the client proposals kept). -/
def recLB (c : Copy) : LB :=
  { clientProposals := match c.lb with
      | some lb => lb.clientProposals
      | none => [],
    maxRecvBallot := -1, prepareOKs := 0, allEqual := false, preAcceptOKs := 0, acceptOKs := 0,
    nacks := 0, originalDeps := nildeps, committedDeps := [], recoveryInst := none,
    preparing := true, numReplicasExecuted := 0, repliedClient := false }

/-- The recovery's own candidate. -/
def recRI (s : RState) (q : w32) (c : Copy) : Option RecoveryInstance :=
  if c.status = St.ACCEPTED then
    some { cmds := c.cmds, status := c.status, seq := c.seq, deps := c.deps, base := c.base,
           preAcceptCount := 0, leaderResponded := false, vbal := c.vbal }
  else if sge c.status St.PREACCEPTED then
    let count : w64 :=
      if c.status = St.PREACCEPTED_EQ ∧ c.vbal = 0 ∧ s.id ≠ q then 1 else 0
    some { cmds := c.cmds, status := c.status, seq := c.seq, deps := c.deps, base := c.base,
           preAcceptCount := count, leaderResponded := (s.id == q), vbal := c.vbal }
  else none

/-- The copy after the recovery trigger. -/
def recCopy (s : RState) (q i : w32) : Copy :=
  let c := recBase s q i
  { c with lb := some { recLB c with recoveryInst := recRI s q c },
           ballot := makeBallotLargerThan s.id c.ballot }

/-- The copy stops the recovery (committed or executed here; no larger ballot). -/
def recStops (c : Copy) : Prop :=
  (c.status = St.COMMITTED ∨ c.status = St.EXECUTED) ∨ sge (c.ballot.sshiftRight 4) maxBallotHi = true

theorem stepRecover_ok (s s' : RState) (q i : w32) (outs : List Out)
    (h : stepRecover s q i = .ok (s', outs)) :
    inBox q i = true ∧
    ((∃ c, s.inst q i = some c ∧ recStops c) ∧ s' = s ∧ outs = [] ∨
     (∀ c, s.inst q i = some c → ¬recStops c) ∧ s' = s.setInst q i (recCopy s q i) ∧
       bcastPrepare (s.setInst q i (recCopy s q i)) q i (recCopy s q i).ballot = some outs) := by
  unfold stepRecover at h
  by_cases hg : (rowOk q && sle 0 i && slt i (s.crt q)) = true
  · simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hb : inBox q i = true
    · refine ⟨hb, ?_⟩
      simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      rcases hc : s.inst q i with _ | c
      · simp only [hc] at h
        right
        refine ⟨by simp, ?_⟩
        split at h
        · next outs' ho =>
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [recCopy, recBase, recLB, recRI, hc, true_and]; exact ho
        · cases h
      · simp only [hc] at h
        by_cases h1 : c.status = St.COMMITTED ∨ c.status = St.EXECUTED
        · simp only [h1, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          exact Or.inl ⟨⟨c, rfl, Or.inl h1⟩, h.1.symm, h.2.symm⟩
        · simp only [h1, ↓reduceIte] at h
          by_cases h2 : sge (c.ballot.sshiftRight 4) maxBallotHi = true
          · simp only [h2, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            exact Or.inl ⟨⟨c, rfl, Or.inr h2⟩, h.1.symm, h.2.symm⟩
          · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
            right
            refine ⟨?_, ?_⟩
            · intro c' hc'; cases hc'; unfold recStops; simp [h1, h2]
            split at h
            · next outs' ho =>
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [recCopy, recBase, recLB, recRI, hc, true_and]
              cases hlb : c.lb <;> simp only [hlb, true_and] at ho ⊢ <;> exact ho
            · cases h
    · simp only [hb, Bool.not_false, ↓reduceIte] at h; cases h
  · simp only [hg, Bool.not_false, ↓reduceIte] at h
    cases h

end Perennial.gryff.replica2.h3

namespace Perennial.gryff.replica2.h3
open Perennial.gryff.model

/-- `handlePrepareReply`'s guards (the code's early returns), then `prMain`. -/
theorem stepPrepareReply_guards (s s' : RState) (m : PrepareReplyM) (outs : List Out)
    (h : stepPrepareReply s m = .ok (s', outs)) :
    inBox m.replica m.inst = true ∧ ∃ c, s.inst m.replica m.inst = some c ∧
      ((match c.lb with | none => true | some lb => !lb.preparing) = true ∧ s' = s ∧ outs = [] ∨
       ∃ lb, c.lb = some lb ∧ lb.preparing = true ∧
        ((c.status = St.COMMITTED ∨ c.status = St.EXECUTED) ∧ s' = s ∧ outs = [] ∨
         ¬(c.status = St.COMMITTED ∨ c.status = St.EXECUTED) ∧
          (m.ok = FALSE ∧ s' = s.setInst m.replica m.inst
              { c with lb := some { lb with nacks := lb.nacks + 1 } } ∧ outs = [] ∨
           m.ok ≠ FALSE ∧ (m.ballot ≠ c.ballot ∧ s' = s ∧ outs = [] ∨
            m.ballot = c.ballot ∧ cmdsOk m.cmds = true ∧ prMain s m c lb = .ok (s', outs))))) := by
  have hcm : cmdsOk m.cmds = true := by
    cases hn : cmdsOk m.cmds
    · unfold stepPrepareReply at h
      simp only [hn, Bool.not_false, ↓reduceIte] at h
      cases h
    · rfl
  have hbox : inBox m.replica m.inst = true := by
    cases hn : inBox m.replica m.inst
    · unfold stepPrepareReply at h
      simp only [hcm, hn, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at h
      cases h
    · rfl
  refine ⟨hbox, ?_⟩
  rcases hc : s.inst m.replica m.inst with _ | c
  · unfold stepPrepareReply at h
    simp only [hcm, hbox, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases h
  refine ⟨c, rfl, ?_⟩
  rcases hl : c.lb with _ | lb
  · unfold stepPrepareReply at h
    simp only [hcm, hbox, hc, hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure,
      Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨rfl, h.1.symm, h.2.symm⟩
  by_cases hp : lb.preparing = true
  rotate_left
  · unfold stepPrepareReply at h
    simp only [Bool.not_eq_true] at hp
    simp only [hcm, hbox, hc, hl, hp, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨by simp [hp], h.1.symm, h.2.symm⟩
  refine Or.inr ⟨lb, rfl, hp, ?_⟩
  by_cases hcs : c.status = St.COMMITTED ∨ c.status = St.EXECUTED
  · unfold stepPrepareReply at h
    simp only [hcm, hbox, hc, hl, hp, hcs, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨hcs, h.1.symm, h.2.symm⟩
  refine Or.inr ⟨hcs, ?_⟩
  by_cases hok : m.ok = FALSE
  · unfold stepPrepareReply at h
    simp only [hcm, hbox, hc, hl, hp, hcs, hok, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨hok, by rw [hp]; exact h.1.symm, h.2.symm⟩
  refine Or.inr ⟨hok, ?_⟩
  by_cases hb : m.ballot = c.ballot
  · refine Or.inr ⟨hb, hcm, ?_⟩
    rw [← stepPrepareReply_main s m c lb hcm hbox hc hl hp hcs hok hb]; exact h
  · unfold stepPrepareReply at h
    simp only [hcm, hbox, hc, hl, hp, hcs, hok, hb, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, ne_eq, not_false_eq_true] at h
    exact Or.inl ⟨hb, h.1.symm, h.2.symm⟩

end Perennial.gryff.replica2.h3
