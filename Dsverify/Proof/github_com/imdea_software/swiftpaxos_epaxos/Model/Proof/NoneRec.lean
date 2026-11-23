/-
(p-link, HANDLERS-5) A NONE record has no commands and no deps (`newInstanceDefault`'s): `NR`.
Every replica step keeps it (`handlePrepare`'s reply carries a record's commands and deps, also
when it reports NONE: they are then empty). A fact of the replicas' states only; it is kept in
`epInvB` with the steps' preservation lemmas below.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Basic

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

namespace NoneRec

/-- A record: NONE only with no commands and no deps. -/
def recOk (w : InstRec) : Prop := w.status = stNONE → w.cmds = none ∧ w.deps = []

/-- Every record of the replica is `recOk`. -/
def NR (σ : RState) : Prop := ∀ x w, σ.inst x = some w → recOk w

/-- Every record but `x`'s is `recOk`. -/
def NRx (σ : RState) (x : InstId) : Prop := ∀ y w, y ≠ x → σ.inst y = some w → recOk w

theorem recOk_of_ne {w : InstRec} (h : w.status ≠ stNONE) : recOk w := fun h' => absurd h' h

theorem NR.toNRx {σ : RState} (h : NR σ) (x : InstId) : NRx σ x := fun y w _ hw => h y w hw

theorem NR_of_inst {σ σ' : RState} (he : σ'.inst = σ.inst) (h : NR σ) : NR σ' := by
  intro y w hw; rw [he] at hw; exact h y w hw

theorem NRx_of_inst {σ σ' : RState} {x : InstId} (he : σ'.inst = σ.inst) (h : NRx σ x) :
    NRx σ' x := by
  intro y w hy hw; rw [he] at hw; exact h y w hy hw

theorem NR_setInst {σ : RState} {x : InstId} {w : InstRec} (h : NRx σ x) (hw : recOk w) :
    NR (σ.setInst x w) := by
  intro y w' hy
  simp only [RState.setInst, upd] at hy
  split at hy
  · cases hy; exact hw
  · exact h y w' (by assumption) hy

theorem NRx_setInst {σ : RState} {x : InstId} {w : InstRec} (h : NRx σ x) :
    NRx (σ.setInst x w) x := by
  intro y w' hy hw'
  simp only [RState.setInst, upd, if_neg hy] at hw'
  exact h y w' hy hw'

@[simp] theorem updateConflicts_inst' (σ : RState) (cmds : List WCmd) (q : Nat) (n seq : w32) :
    (updateConflicts σ cmds q n seq).inst = σ.inst := by
  unfold updateConflicts
  generalize σ = τ
  induction cmds generalizing τ with
  | nil => rfl
  | cons c cs ih => simp only [List.foldl_cons]; rw [ih]

@[simp] theorem updateCommitted_inst' (σ : RState) (q : Nat) : (updateCommitted σ q).inst = σ.inst :=
  rfl

@[simp] theorem bumpRecvBallot_inst' (σ : RState) (b : w32) : (bumpRecvBallot σ b).inst = σ.inst := by
  unfold bumpRecvBallot; split <;> rfl

@[simp] theorem bumpCrt_inst' (σ : RState) (q : Nat) (n : w32) : (bumpCrt σ q n).inst = σ.inst := by
  unfold bumpCrt; split <;> rfl

theorem recOk_default (x : InstId) : recOk (newInstanceDefault x) := fun _ => ⟨rfl, rfl⟩

theorem getOrDefault_NR {σ : RState} (h : NR σ) (x : InstId) :
    NR (getOrDefault σ x).1 ∧ recOk (getOrDefault σ x).2 := by
  unfold getOrDefault
  split
  · rename_i w hw; exact ⟨h, h x w hw⟩
  · exact ⟨NR_setInst (h.toNRx x) (recOk_default x), recOk_default x⟩

theorem getOrDefault_NRx {σ : RState} {x : InstId} (h : NRx σ x) :
    NRx (getOrDefault σ x).1 x := by
  unfold getOrDefault
  split
  · exact h
  · exact NRx_setInst h

theorem startPhase1_NR {σ : RState} {x : InstId} (h : NRx σ x) (cmds : List WCmd)
    (replica n ballot : w32) (ps : Option (List Proposal)) :
    NR (startPhase1 σ cmds x replica n ballot ps).1 := by
  intro y w hy
  unfold startPhase1 at hy
  simp only [] at hy
  split at hy <;>
  · simp only [updateConflicts_inst', RState.setInst] at hy
    by_cases hyx : y = x
    · subst hyx; simp only [upd_same, Option.some.injEq] at hy; subst hy
      exact recOk_of_ne (by simp [stPREACCEPTED, stNONE])
    · rw [upd_other _ _ _ _ hyx] at hy; exact h y w hyx hy

theorem bump_NR {σ : RState} (h : NR σ) (b : w32) : NR (bumpRecvBallot σ b) :=
  NR_of_inst (by simp) h

theorem hPrepare_NR {σ : RState} (h : NR σ) (m : Prepare) : NR (hPrepare σ m).1 := by
  unfold hPrepare
  obtain ⟨h2, h3⟩ := getOrDefault_NR (bump_NR h m.ballot) ⟨toN m.replica, toN m.inst⟩
  apply NR_setInst (h2.toNRx _)
  split
  · exact fun hs => h3 hs
  · exact h3

theorem NR_upd_inst {σ' σ : RState} {x : InstId} {w : InstRec}
    (he : σ'.inst = (σ.setInst x w).inst) (h : NRx σ x) (hw : recOk w) : NR σ' :=
  NR_of_inst he (NR_setInst h hw)

theorem stGe_ne {s t : w8} (ht : t ≠ stNONE) (htz : 0 < sint.Z t) (h : stGe s t = true) :
    s ≠ stNONE := by
  intro e; rw [e] at h; unfold stGe at h
  have := (BitVec.sle_iff_toInt_le).1 h
  simp [stNONE, sint.Z] at this htz; omega

theorem hPreAccept_NR {σ : RState} (h : NR σ) (m : PreAccept) : NR (hPreAccept σ m).1 := by
  unfold hPreAccept
  simp only []
  generalize hσ1 : bumpCrt (bumpRecvBallot (if σ.maxSeq.sle m.seq = true then
    { σ with maxSeq := m.seq + 1 } else σ) m.ballot) (toN m.replica) m.inst = σ1
  have h1 : NR σ1 := by
    rw [← hσ1]; refine NR_of_inst ?_ h; simp only [bumpCrt_inst', bumpRecvBallot_inst']
    split <;> rfl
  obtain ⟨h2, h3⟩ := getOrDefault_NR h1 ⟨toN m.replica, toN m.inst⟩
  split
  · exact h2
  · split
    · split
      · dsimp only
        apply NR_upd_inst
        · (try simp only [updateConflicts_inst', updateCommitted_inst']); (try rfl)
        · exact h2.toNRx _
        · exact recOk_of_ne (stGe_ne (t := stACCEPTED) (by decide) (by decide) (by assumption))
      · exact NR_setInst (h2.toNRx _) (fun hs => h3 hs)
    · dsimp only
      apply NR_upd_inst
      · (try simp only [updateConflicts_inst', updateCommitted_inst']); (try rfl)
      · exact h2.toNRx _
      · apply recOk_of_ne; dsimp only; split <;> simp [stPREACCEPTED, stPREACCEPTED_EQ, stNONE]

theorem hAccept_NR {σ : RState} (h : NR σ) (m : Accept) : NR (hAccept σ m).1 := by
  unfold hAccept
  simp only []
  have h1 : NR (bumpCrt (bumpRecvBallot σ m.ballot) (toN m.replica) m.inst) :=
    NR_of_inst (by simp) h
  obtain ⟨h2, h3⟩ := getOrDefault_NR h1 ⟨toN m.replica, toN m.inst⟩
  split
  · exact h2
  · split
    · exact h2
    · exact NR_setInst (h2.toNRx _) (recOk_of_ne (by simp [stACCEPTED, stCOMMITTED, stPREACCEPTED, stPREACCEPTED_EQ, stNONE, stEXECUTED]))

theorem hCommit_NR {σ : RState} (h : NR σ) (m : Commit) : NR (hCommit σ m).1 := by
  unfold hCommit
  simp only []
  have h1 : NR (bumpRecvBallot (bumpCrt σ (toN m.replica) m.inst) m.ballot) :=
    NR_of_inst (by simp) h
  obtain ⟨h2, h3⟩ := getOrDefault_NR h1 ⟨toN m.replica, toN m.inst⟩
  split
  · exact h2
  · split
    · exact h2
    · dsimp only
      apply NR_upd_inst
      · (try simp only [updateConflicts_inst', updateCommitted_inst']); (try rfl)
      · exact h2.toNRx _
      · exact recOk_of_ne (by simp [stACCEPTED, stCOMMITTED, stPREACCEPTED, stPREACCEPTED_EQ, stNONE, stEXECUTED])

theorem NR_ite {c : Prop} [Decidable c] {a b : RState × List Out} (ha : c → NR a.1)
    (hb : ¬c → NR b.1) : NR (if c then a else b).1 := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

set_option hygiene false in
/-- Close an `NR` goal of a handler's branch: the state as it was (`hb`), a record update keeping
the record's status/commands/deps (`hi`), a new record past NONE, `startPhase1`, the nack branch. -/
macro "nr_close" : tactic => `(tactic| first
  | exact hb
  | exact NR_setInst (hb.toNRx _) (fun hs => hi hs)
  | exact startPhase1_NR (NRx_setInst (hb.toNRx _)) _ _ _ _ _
  | exact nackBranch_NR hb hi _ _
  | (apply NR_upd_inst
     · (try simp only [updateConflicts_inst', updateCommitted_inst']); (try rfl)
     · exact hb.toNRx _
     · exact recOk_of_ne (by simp [stACCEPTED, stCOMMITTED, stPREACCEPTED, stPREACCEPTED_EQ, stNONE, stEXECUTED])))

theorem nackBranch_NR {σ : RState} {inst : InstRec} (hb : NR σ) (hi : recOk inst) (x : InstId)
    (lb : LbRec) : NR (nackBranch σ x inst lb).1 := by
  unfold nackBranch
  dsimp only
  split
  · split <;> exact NR_setInst (hb.toNRx _) (fun hs => hi hs)
  · exact NR_setInst (hb.toNRx _) (fun hs => hi hs)

theorem hPrepareReply_NR {σ : RState} (h : NR σ) (m : PrepareReply) :
    NR (hPrepareReply σ m).1 := by
  unfold hPrepareReply
  dsimp only
  split
  · exact h
  rename_i inst hinst
  split
  · exact h
  have hb := bump_NR h m.ballot
  have hi : recOk inst := h _ _ hinst
  repeat' (apply NR_ite <;> intro _)
  all_goals nr_close

theorem hPreAcceptReply_NR {σ : RState} (h : NR σ) (m : PreAcceptReply) :
    NR (hPreAcceptReply σ m).1 := by
  unfold hPreAcceptReply
  dsimp only
  split
  · exact h
  rename_i inst hinst
  split
  · exact h
  have hb := bump_NR h m.ballot
  have hi : recOk inst := h _ _ hinst
  repeat' (apply NR_ite <;> intro _)
  all_goals nr_close

theorem hAcceptReply_NR {σ : RState} (h : NR σ) (m : AcceptReply) :
    NR (hAcceptReply σ m).1 := by
  unfold hAcceptReply
  dsimp only
  split
  · exact h
  rename_i inst hinst
  split
  · exact h
  have hb := bump_NR h m.ballot
  have hi : recOk inst := h _ _ hinst
  repeat' (apply NR_ite <;> intro _)
  all_goals nr_close

theorem hRecover_NR {σ : RState} (h : NR σ) (x : InstId) : NR (hRecover σ x).1 := by
  unfold hRecover
  obtain ⟨hb, hi⟩ := getOrDefault_NR h x
  dsimp only
  repeat' split
  all_goals nr_close

theorem hPropose_NR {σ : RState} (h : NR σ) (batch : List Proposal) :
    NR (hPropose σ batch).1 := by
  unfold hPropose
  split
  · exact h
  · have h' : NR { σ with crtInstance := upd σ.crtInstance σ.id (σ.crtInstance σ.id + 1) } :=
      NR_of_inst rfl h
    dsimp only
    apply startPhase1_NR
    exact h'.toNRx _

theorem bcastRep_NR {σ : RState} (h : NR σ) (b : Bcast) (a : Bool) : NR (bcastRep σ b a) := by
  unfold bcastRep
  split
  · unfold setPreAcceptsSent
    split
    · rename_i w hw
      split
      · exact NR_setInst (h.toNRx _) (fun hs => (h _ w hw : recOk w) hs)
      · exact h
    · exact h
  · exact h

theorem execDone_NR {σ : RState} (h : NR σ) (x : InstId) : NR (execDone σ x) := by
  unfold execDone
  split
  · exact NR_setInst (h.toNRx _) (recOk_of_ne (by simp [stACCEPTED, stCOMMITTED, stPREACCEPTED, stPREACCEPTED_EQ, stNONE, stEXECUTED]))
  · exact h

theorem execCmdAt_NR {σ : RState} (h : NR σ) (w : InstRec) (idx : Nat) :
    NR (execCmdAt σ w idx).1 := by
  unfold execCmdAt
  dsimp only
  repeat' split
  all_goals first | exact h | exact NR_of_inst rfl h

theorem hMsg_NR {σ : RState} (h : NR σ) (m : Msg) : NR (hMsg σ m).1 := by
  cases m with
  | prepare p => exact hPrepare_NR h p
  | prepareReply p => exact hPrepareReply_NR h p
  | preAccept p => exact hPreAccept_NR h p
  | preAcceptReply p => exact hPreAcceptReply_NR h p
  | accept p => exact hAccept_NR h p
  | acceptReply p => exact hAcceptReply_NR h p
  | commit p => exact hCommit_NR h p
  | tryPreAccept p => exact h
  | tryPreAcceptReply p => exact h
  | beacon _ => exact h
  | beaconReply _ => exact h

end NoneRec

open NoneRec

/-- (p-link, HANDLERS-5) What `epInvB` keeps of the system beyond `Inv`: NONE records are empty
(`NR`), and every instance's batch is shorter than `2 ^ 62` (its proposals came from a Go slice
of at most `ProposeChan`'s capacity plus one; the model's `propose` step does not bound it). -/
def InvX (S : Sys) : Prop :=
  (∀ r, NR (S.rep r)) ∧ ∀ x ps, S.owner x = some ps → ps.length < 2 ^ 62

theorem InvX_init : InvX Sys.init := by
  refine ⟨fun r x w h => ?_, fun x ps h => ?_⟩
  · simp [Sys.init, RState.init] at h
  · simp [Sys.init] at h

theorem InvX_rep_upd {S S' : Sys} (h : InvX S) {i : Nat} {σ' : RState} (hσ : NR σ')
    (hrep : S'.rep = upd S.rep i σ') (hown : S'.owner = S.owner) : InvX S' := by
  refine ⟨fun r => ?_, fun x ps hx => h.2 x ps (by rw [← hown]; exact hx)⟩
  rw [hrep]; unfold upd; split
  · exact hσ
  · exact h.1 r

theorem InvX_rep_eq {S S' : Sys} (h : InvX S) (hrep : S'.rep = S.rep)
    (hown : S'.owner = S.owner) : InvX S' := by
  refine ⟨fun r => ?_, fun x ps hx => h.2 x ps (by rw [← hown]; exact hx)⟩
  rw [hrep]; exact h.1 r

namespace NoneRec
end NoneRec

theorem NR_updAll {S : Sys} (h : ∀ r, NR (S.rep r)) {i : Nat} {σ' : RState} (hσ : NR σ') :
    ∀ r, NR (upd S.rep i σ' r) := by
  intro r; unfold upd; split
  · exact hσ
  · exact h r

theorem applyStep_rep' (S : Sys) (i : Nat) (r : RState × List Out) :
    (S.applyStep i r).rep = upd S.rep i r.1 := by
  unfold Sys.applyStep; rw [Sys.foldl_emit_rep]

theorem fire_rep (S : Sys) (e : Slot × WCmd) :
    (S.fire e).rep = S.rep := by
  unfold Sys.fire
  split
  · rfl
  · dsimp only; split <;> rfl

theorem applyStep_owner' (S : Sys) (i : Nat) (r : RState × List Out) :
    (S.applyStep i r).owner = S.owner := by
  unfold Sys.applyStep; rw [Sys.foldl_emit_owner]

theorem fire_owner (S : Sys) (e : Slot × WCmd) :
    (S.fire e).owner = S.owner := by
  unfold Sys.fire
  split
  · rfl
  · dsimp only; split <;> rfl

theorem execCmd_owner (S : Sys) (i : Nat) (x : InstId) (w : InstRec) :
    (S.execCmd i x w).owner = S.owner := by
  unfold Sys.execCmd; dsimp only
  split
  · exact applyStep_owner' _ _ _
  · rw [fire_owner]; exact applyStep_owner' _ _ _

/-- Every step keeps `NR` of every replica. -/
theorem NR_step {S S' : Sys} (hs : Step S S') (h : ∀ r, NR (S.rep r)) : ∀ r, NR (S'.rep r) := by
  cases hs with
  | clientPropose => exact h
  | propose i batch =>
    unfold Sys.propose
    dsimp only
    split <;>
    · simp only [applyStep_rep']
      exact NR_updAll h (hPropose_NR (h i) batch)
  | deliver fr i n m =>
    unfold Sys.deliver; simp only [applyStep_rep']
    exact NR_updAll h (hMsg_NR (h i) m)
  | recover i x =>
    simp only [applyStep_rep']
    exact NR_updAll h (hRecover_NR (h i) x)
  | bcastStep i b a =>
    unfold Sys.bcastStep
    have h1 : ∀ r, NR (upd S.rep i (bcastRep (S.rep i) b a) r) := NR_updAll h (bcastRep_NR (h i) b a)
    split <;> first | exact h1 | (simp only [Sys.emit]; exact h1)
  | beTheLeader i => exact NR_updAll h (NR_of_inst rfl (h i))
  | peerOrder i o => exact NR_updAll h (NR_of_inst rfl (h i))
  | flush => exact h
  | lose => exact h
  | execSCC => exact h
  | execCmd i x rest w =>
    unfold Sys.execCmd
    dsimp only
    have h1 : ∀ r, NR (upd S.rep i (execCmdAt (S.rep i) w (S.execIdx i)).1 r) :=
      NR_updAll h (execCmdAt_NR (h i) w _)
    split
    · simp only [applyStep_rep']; exact h1
    · rw [fire_rep]; simp only [applyStep_rep']; exact h1
  | instDone i x rest => exact NR_updAll h (execDone_NR (h i) x)
  | execBump i q => exact NR_updAll h (NR_of_inst rfl (h i))

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
