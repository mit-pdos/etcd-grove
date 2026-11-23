/-
`step_crt_mono`: `crtInstance` only grows. Every helper leaves it or raises it (`bumpCrt`); the
only other write is `handlePropose`'s increment, below the row's capacity (`Inv.wf` bounds
`crtInstance`, so `+ 1` does not wrap).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Basic

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace CrtProof

/-- `bumpCrt`'s effect on `crtInstance`. -/
def crtBump (c : Nat → w32) (q : Nat) (n : w32) : Nat → w32 := if (c q).slt n then upd c q n else c
theorem bumpCrt_crt (σ : RState) (q : Nat) (n : w32) : (bumpCrt σ q n).crtInstance = crtBump σ.crtInstance q n := by
  unfold bumpCrt crtBump; split <;> simp_all
@[simp] theorem updateConflicts_crt (σ : RState) (cmds : List WCmd) (q : Nat) (n seq : w32) :
    (updateConflicts σ cmds q n seq).crtInstance = σ.crtInstance := by
  unfold updateConflicts
  induction cmds generalizing σ with
  | nil => rfl
  | cons c cs ih => rw [List.foldl_cons, ih]
@[simp] theorem getOrDefault_crt (σ : RState) (x : InstId) :
    (getOrDefault σ x).1.crtInstance = σ.crtInstance := by
  unfold getOrDefault; split <;> rfl
@[simp] theorem bumpRecvBallot_crt (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).crtInstance = σ.crtInstance := by
  unfold bumpRecvBallot; split <;> rfl
@[simp] theorem updateCommitted_crt (σ : RState) (q : Nat) :
    (updateCommitted σ q).crtInstance = σ.crtInstance := rfl
@[simp] theorem setInst_crt (σ : RState) (x : InstId) (w : InstRec) :
    (σ.setInst x w).crtInstance = σ.crtInstance := rfl
@[simp] theorem startPhase1_crt (σ : RState) (cmds : List WCmd) (x : InstId) (r n b : w32)
    (ps : Option (List Proposal)) : (startPhase1 σ cmds x r n b ps).1.crtInstance = σ.crtInstance := by
  unfold startPhase1
  simp only
  split <;> simp
@[simp] theorem nackBranch_crt (σ : RState) (x : InstId) (w : InstRec) (lb : LbRec) :
    (nackBranch σ x w lb).1.crtInstance = σ.crtInstance := by
  unfold nackBranch
  simp only
  split
  · split <;> rfl
  · rfl
@[simp] theorem ite_fst_crt (c : Prop) [Decidable c] (a b : RState × List Out) :
    (if c then a else b).1.crtInstance = if c then a.1.crtInstance else b.1.crtInstance := by
  split <;> rfl
theorem hPreAccept_crt (σ : RState) (m : PreAccept) :
    (hPreAccept σ m).1.crtInstance = crtBump σ.crtInstance (toN m.replica) m.inst := by
  unfold hPreAccept
  simp only
  generalize hg : getOrDefault _ _ = g
  have hc : g.1.crtInstance = crtBump σ.crtInstance (toN m.replica) m.inst := by
    rw [← hg, getOrDefault_crt, bumpCrt_crt, bumpRecvBallot_crt]; split <;> rfl
  obtain ⟨σ3, w⟩ := g
  simp only at hc ⊢
  split
  · exact hc
  · split <;> (try split) <;> simp [hc]

theorem hPreAcceptReply_crt (σ : RState) (m : PreAcceptReply) :
    (hPreAcceptReply σ m).1.crtInstance = σ.crtInstance := by
  unfold hPreAcceptReply
  dsimp only
  split
  · rfl
  · split
    · rfl
    · simp
theorem hAcceptReply_crt (σ : RState) (m : AcceptReply) :
    (hAcceptReply σ m).1.crtInstance = σ.crtInstance := by
  unfold hAcceptReply
  dsimp only
  split
  · rfl
  · split
    · rfl
    · simp
theorem hPrepareReply_crt (σ : RState) (m : PrepareReply) :
    (hPrepareReply σ m).1.crtInstance = σ.crtInstance := by
  unfold hPrepareReply
  dsimp only
  split
  · rfl
  · split
    · rfl
    · simp
theorem hPrepare_crt (σ : RState) (m : Prepare) :
    (hPrepare σ m).1.crtInstance = σ.crtInstance := by
  unfold hPrepare
  simp only
  generalize hg : getOrDefault _ _ = g
  have hc : g.1.crtInstance = σ.crtInstance := by rw [← hg]; simp
  obtain ⟨σ3, w⟩ := g
  simp only at hc ⊢
  split <;> simp [hc]
theorem hRecover_crt (σ : RState) (x : InstId) :
    (hRecover σ x).1.crtInstance = σ.crtInstance := by
  unfold hRecover
  generalize hg : getOrDefault _ _ = g
  have hc : g.1.crtInstance = σ.crtInstance := by rw [← hg]; simp
  obtain ⟨σ3, w⟩ := g
  simp only at hc ⊢
  repeat' split
  all_goals simp [hc]
theorem hAccept_crt (σ : RState) (m : Accept) :
    (hAccept σ m).1.crtInstance = crtBump σ.crtInstance (toN m.replica) m.inst := by
  unfold hAccept
  simp only
  generalize hg : getOrDefault _ _ = g
  have hc : g.1.crtInstance = crtBump σ.crtInstance (toN m.replica) m.inst := by
    rw [← hg, getOrDefault_crt, bumpCrt_crt, bumpRecvBallot_crt]
  obtain ⟨σ3, w⟩ := g
  simp only at hc ⊢
  repeat' split
  all_goals simp [hc]
theorem hCommit_crt (σ : RState) (m : Commit) :
    (hCommit σ m).1.crtInstance = crtBump σ.crtInstance (toN m.replica) m.inst := by
  unfold hCommit
  simp only
  generalize hg : getOrDefault _ _ = g
  have hc : g.1.crtInstance = crtBump σ.crtInstance (toN m.replica) m.inst := by
    rw [← hg, getOrDefault_crt, bumpRecvBallot_crt, bumpCrt_crt]
  obtain ⟨σ3, w⟩ := g
  simp only at hc ⊢
  repeat' split
  all_goals simp [hc]

theorem crtBump_le (c : Nat → w32) (q : Nat) (n : w32) (q' : Nat) :
    zz (c q') ≤ zz (crtBump c q n q') := by
  unfold crtBump
  split
  · rename_i h
    by_cases hq : q' = q
    · subst hq; simp only [upd_same]
      have := (BitVec.slt_iff_toInt_lt).mp (by simpa using h)
      simp only [zz, sint.Z]; omega
    · simp [upd_other _ _ _ _ hq]
  · exact Int.le_refl _

theorem hMsg_crt_le (σ : RState) (m : Msg) (q : Nat) :
    zz (σ.crtInstance q) ≤ zz ((hMsg σ m).1.crtInstance q) := by
  cases m <;> simp only [hMsg]
  case prepare p => rw [hPrepare_crt]; exact Int.le_refl _
  case prepareReply p => rw [hPrepareReply_crt]; exact Int.le_refl _
  case preAccept p => rw [hPreAccept_crt]; exact crtBump_le _ _ _ _
  case preAcceptReply p => rw [hPreAcceptReply_crt]; exact Int.le_refl _
  case accept p => rw [hAccept_crt]; exact crtBump_le _ _ _ _
  case acceptReply p => rw [hAcceptReply_crt]; exact Int.le_refl _
  case commit p => rw [hCommit_crt]; exact crtBump_le _ _ _ _
  all_goals exact Int.le_refl _

theorem hPropose_crt_le (σ : RState) (batch : List Proposal) (q : Nat)
    (hb : -1 ≤ zz (σ.crtInstance σ.id) ∧ toN (σ.crtInstance σ.id) + 1 < MAX_INSTANCE) :
    zz (σ.crtInstance q) ≤ zz ((hPropose σ batch).1.crtInstance q) := by
  unfold hPropose
  split
  · exact Int.le_refl _
  · simp only [startPhase1_crt]
    by_cases hq : q = σ.id
    · subst hq; simp only [upd_same]
      simp only [zz, sint.Z, toN, MAX_INSTANCE] at hb ⊢
      rw [BitVec.toInt_add_of_not_saddOverflow]
      · simp; omega
      · simp only [BitVec.saddOverflow]
        simp; omega
    · simp [upd_other _ _ _ _ hq]

@[simp] theorem setPreAcceptsSent_crt (σ : RState) (x : InstId) (n : Nat) :
    (setPreAcceptsSent σ x n).crtInstance = σ.crtInstance := by
  unfold setPreAcceptsSent; split
  · split <;> rfl
  · rfl

@[simp] theorem bcastRep_crt (σ : RState) (b : Bcast) (a : Bool) :
    (bcastRep σ b a).crtInstance = σ.crtInstance := by
  unfold bcastRep; split <;> simp

@[simp] theorem execDone_crt (σ : RState) (x : InstId) :
    (execDone σ x).crtInstance = σ.crtInstance := by
  unfold execDone; split <;> rfl

@[simp] theorem execCmdAt_crt (σ : RState) (w : InstRec) (idx : Nat) :
    (execCmdAt σ w idx).1.crtInstance = σ.crtInstance := by
  unfold execCmdAt; dsimp only; split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem fire_rep (S : Sys) (e : Slot × WCmd) :
    (S.fire e).rep = S.rep := by
  unfold Sys.fire
  split
  · rfl
  · dsimp only; split <;> rfl

theorem upd_crt_le (R : Nat → RState) (i : Nat) (σ' : RState) (j q : Nat)
    (h : zz ((R i).crtInstance q) ≤ zz (σ'.crtInstance q)) :
    zz ((R j).crtInstance q) ≤ zz ((upd R i σ' j).crtInstance q) := by
  by_cases hj : j = i
  · subst hj; simpa using h
  · simp [upd_other _ _ _ _ hj]

end CrtProof

open CrtProof in
theorem step_crt_mono' (S S' : Sys) (hS : Inv0 S) (h : Step S S') (i q : Nat) :
    zz ((S.rep i).crtInstance q) ≤ zz ((S'.rep i).crtInstance q) := by
  cases h with
  | clientPropose => exact Int.le_refl _
  | propose j batch hj =>
    simp only [Sys.propose]
    rw [show ∀ S2 : Sys, S2.applyStep j (hPropose (S.rep j) batch) =
      S2.applyStep j ((hPropose (S.rep j) batch).1, (hPropose (S.rep j) batch).2) from fun _ => rfl]
    simp only [Sys.applyStep_rep]
    have hrep : (if rowFull (S.rep j) = true then
        { S with proposeChan := upd S.proposeChan j ((S.proposeChan j).diff batch) }
        else { S with proposeChan := upd S.proposeChan j ((S.proposeChan j).diff batch),
                      owner := upd S.owner ⟨j, toN ((S.rep j).crtInstance j + 1)⟩ (some batch) }).rep
        = S.rep := by split <;> rfl
    rw [hrep]
    refine upd_crt_le _ _ _ _ _ (hPropose_crt_le _ _ _ ?_)
    have hid := hS.1.1 j hj
    rw [hid]; exact hS.1.2.2.1 j hj j hj
  | deliver fr j n m hj =>
    simp only [Sys.deliver]
    rw [show ∀ S2 : Sys, S2.applyStep j (hMsg (S.rep j) m) =
      S2.applyStep j ((hMsg (S.rep j) m).1, (hMsg (S.rep j) m).2) from fun _ => rfl]
    simp only [Sys.applyStep_rep]
    exact upd_crt_le _ _ _ _ _ (hMsg_crt_le _ _ _)
  | recover j x =>
    rw [show S.applyStep j (hRecover (S.rep j) x) =
      S.applyStep j ((hRecover (S.rep j) x).1, (hRecover (S.rep j) x).2) from rfl]
    simp only [Sys.applyStep_rep]
    exact upd_crt_le _ _ _ _ _ (by rw [hRecover_crt]; exact Int.le_refl _)
  | bcastStep j b a =>
    simp only [Sys.bcastStep]
    split
    · simp only [Sys.emit]; exact upd_crt_le _ _ _ _ _ (by simp)
    · exact upd_crt_le _ _ _ _ _ (by simp)
  | beTheLeader j => exact upd_crt_le _ _ _ _ _ (Int.le_refl _)
  | peerOrder j o => exact upd_crt_le _ _ _ _ _ (Int.le_refl _)
  | flush => exact Int.le_refl _
  | lose => exact Int.le_refl _
  | execSCC => exact Int.le_refl _
  | execCmd j x rest w =>
    simp only [Sys.execCmd]
    rw [show S.applyStep j (execCmdAt (S.rep j) w (S.execIdx j)) =
      S.applyStep j ((execCmdAt (S.rep j) w (S.execIdx j)).1,
        (execCmdAt (S.rep j) w (S.execIdx j)).2) from rfl]
    split
    · simp only [Sys.applyStep_rep]
      exact upd_crt_le _ _ _ _ _ (by simp)
    · rw [fire_rep]; simp only [Sys.applyStep_rep]
      exact upd_crt_le _ _ _ _ _ (by simp)
  | instDone j x rest w =>
    exact upd_crt_le _ _ _ _ _ (by simp)
  | execBump j q' => exact upd_crt_le _ _ _ _ _ (Int.le_refl _)

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
