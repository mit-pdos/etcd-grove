/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureT/Ghost.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A2: the model's ghost fields (hub request R-I-1, unit I): only client requests change
`nReqs` (by one) and `used` (by the request's key), in any state.
-/
module

public import Dsverify.Proof.gryff.PureT.Total

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.tot

open model kahn

/-- `s'` has `s`'s ghost fields. -/
def GhostEq (s s' : RState) : Prop := s'.nReqs = s.nReqs ∧ s'.used = s.used

theorem GhostEq.refl (s : RState) : GhostEq s s := ⟨rfl, rfl⟩
theorem GhostEq.trans {s1 s2 s3 : RState} (a : GhostEq s1 s2) (b : GhostEq s2 s3) :
    GhostEq s1 s3 := ⟨b.1.trans a.1, b.2.trans a.2⟩

section
variable (s : RState) (q i x seq : w32) (c : Copy) (cmds : List Cmd)
@[simp] theorem setInst_nReqs : (s.setInst q i c).nReqs = s.nReqs := rfl
@[simp] theorem setInst_used : (s.setInst q i c).used = s.used := rfl
@[simp] theorem setCrt_nReqs : (s.setCrt q x).nReqs = s.nReqs := rfl
@[simp] theorem setCrt_used : (s.setCrt q x).used = s.used := rfl
@[simp] theorem updConf_nReqs : (updateConflicts s cmds q i seq).nReqs = s.nReqs := by
  obtain ⟨cf, ms, he, -⟩ := updateConflicts_eq s cmds q i seq; rw [he]
@[simp] theorem updConf_used : (updateConflicts s cmds q i seq).used = s.used := by
  obtain ⟨cf, ms, he, -⟩ := updateConflicts_eq s cmds q i seq; rw [he]
end

theorem ghost_updCommitted {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    GhostEq s s' := by
  obtain ⟨cu, rfl⟩ := updateCommitted_form h; exact ⟨rfl, rfl⟩

set_option hygiene false in
/-- Closes a leaf `h : <result> = .ok res ⊢ GhostEq s res.1`. -/
macro "gleaf" : tactic => `(tactic| first
  | (cases h; done)
  | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp [GhostEq]; done)
  | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp [GhostEq, RState.overwrite]; done)
  | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; unfold RState.overwrite; split <;> simp [GhostEq]; done))

set_option hygiene false in
/-- `gleaf`, after resolving an `updateCommitted` result. -/
macro "gleafc" : tactic => `(tactic| first
  | gleaf
  | (obtain ⟨cu, rfl⟩ := updateCommitted_form ‹updateCommitted _ _ = some _›
     simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp [GhostEq]; done))

theorem ghost_startPhase1 (S : RState) (q i b : w32) (ps : List Proposal) (cmds : List Cmd)
    {res : RState × List Out} (h : startPhase1 S q i b ps cmds = .ok res) : GhostEq S res.1 := by
  tsimp [startPhase1] at h
  repeat' split at h
  all_goals gleaf

theorem ghost_leaderCommit (S : RState) (q i : w32) (c : Copy) (lb : LB)
    {res : RState × List Out} (h : leaderCommit S q i c lb = .ok res) : GhostEq S res.1 := by
  tsimp [leaderCommit] at h
  repeat' split at h
  all_goals gleafc

theorem ghost_handleExecuted (S : RState) (m : ExecutedM)
    {res : RState × List Out} (h : handleExecuted S m = .ok res) : GhostEq S res.1 := by
  tsimp [handleExecuted] at h
  repeat' split at h
  all_goals gleaf

theorem ex_bind_ok {α β : Type} {x : Except Fail α} {f : α → Except Fail β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem opt_forIn_inv {α β : Type} (l : List α) (init : β) (f : α → β → Option (ForInStep β))
    (I : β → Prop) (h0 : I init)
    (hs : ∀ a b r, I b → f a b = some r → I r.value) {res : β}
    (h : forIn l init f = some res) : I res := by
  induction l generalizing init with
  | nil => simp at h; subst h; exact h0
  | cons a l ih =>
    rw [List.forIn_cons] at h
    cases hf : f a init with
    | none => rw [hf] at h; cases h
    | some r =>
      rw [hf] at h
      have hr := hs a init r h0 hf
      cases r with
      | done b => simp at h; subst h; exact hr
      | yield b => exact ih b hr h

theorem ex_forIn_inv {α β : Type} (l : List α) (init : β) (f : α → β → Except Fail (ForInStep β))
    (I : β → Prop) (h0 : I init)
    (hs : ∀ a b r, I b → f a b = .ok r → I r.value) {res : β}
    (h : forIn l init f = .ok res) : I res := by
  induction l generalizing init with
  | nil => simp [pure, Except.pure] at h; subst h; exact h0
  | cons a l ih =>
    rw [List.forIn_cons] at h
    cases hf : f a init with
    | error e => rw [hf] at h; cases h
    | ok r =>
      rw [hf] at h
      have hr := hs a init r h0 hf
      cases r with
      | done b => simp [bind, Except.bind, pure, Except.pure] at h; subst h; exact hr
      | yield b => exact ih b hr h

theorem opt_bind_some {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem ghost_shortCircuit {s s' : RState} {n : w32} {v : ValTag} {b : Bool} {o : List Out}
    (h : shortCircuit s n v b = some (s', o)) : GhostEq s s' := by
  unfold shortCircuit at h
  split at h
  · simp only [] at h
    obtain ⟨x, hx, hf⟩ := opt_bind_some h
    have hI := opt_forIn_inv _ _ _ (fun b => GhostEq s b.1) ⟨rfl, rfl⟩ (by
        intro a b r hb hr
        split at hr
        · simp at hr; subst hr; exact hb
        · split at hr
          · split at hr
            · simp at hr; subst hr; exact ⟨hb.1, hb.2⟩
            · simp at hr; subst hr; exact hb
          · simp at hr; subst hr; exact hb) hx
    split at hf
    · split at hf
      · simp only [pure, Option.some.injEq, Prod.mk.injEq] at hf; obtain ⟨rfl, rfl⟩ := hf; exact hI
      · cases hf
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at hf; obtain ⟨rfl, rfl⟩ := hf; exact hI
  · cases h

set_option hygiene false in
/-- A leaf of a step's inversion. -/
macro "gall" : tactic => `(tactic| first
  | gleafc
  | (refine GhostEq.trans ?_ (ghost_leaderCommit _ _ _ _ _ h); simp [GhostEq]; done)
  | (refine GhostEq.trans ?_ (ghost_startPhase1 _ _ _ _ _ _ h); simp [GhostEq]; done)
  | (refine GhostEq.trans ?_ (ghost_handleExecuted _ _ h); unfold RState.overwrite; split <;> simp [GhostEq]; done)
  | (refine GhostEq.trans ?_ (ghost_handleExecuted _ _ h); simp [GhostEq]; done))

theorem ghost_stepRead1 (s : RState) (m : Read1ProxiedM) {res : RState × List Out}
    (h : stepRead1 s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepRead1] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_stepRead2 (s : RState) (m : Read2ProxiedM) {res : RState × List Out}
    (h : stepRead2 s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepRead2] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_stepWrite1 (s : RState) (m : Write1ProxiedM) {res : RState × List Out}
    (h : stepWrite1 s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepWrite1] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_stepWrite2 (s : RState) (m : Write2ProxiedM) {res : RState × List Out}
    (h : stepWrite2 s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepWrite2] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_stepRead1Reply (s : RState) (m : Read1ReplyM) {res : RState × List Out}
    (h : stepRead1Reply s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepRead1Reply] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_stepRead2Reply (s : RState) (m : Read2ReplyM) {res : RState × List Out}
    (h : stepRead2Reply s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepRead2Reply] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_stepPrepare (s : RState) (m : PrepareM) {res : RState × List Out}
    (h : stepPrepare s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepPrepare] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_stepPreAccept (s : RState) (m : PreAcceptM) {res : RState × List Out}
    (h : stepPreAccept s m = .ok res) : GhostEq s res.1 := by
  by_cases h1 : cmdsOk m.cmds = true
  · by_cases h2 : inBox m.replica m.inst = true
    · by_cases h3 : sge m.inst (s.crt m.replica) = true
      all_goals cases hc : s.inst m.replica m.inst
      all_goals tsimp [stepPreAccept, h1, h2, h3, hc] at h
      all_goals revert h
      all_goals repeat' split
      all_goals intro h
      all_goals gall
    · tsimp [stepPreAccept, h1, h2] at h; cases h
  · tsimp [stepPreAccept, h1] at h; cases h

theorem ghost_stepAccept (s : RState) (m : EAcceptM) {res : RState × List Out}
    (h : stepAccept s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepAccept] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_stepCommit (s : RState) (m : ECommitM) {res : RState × List Out}
    (h : stepCommit s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepCommit] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_stepPreAcceptReply (s : RState) (m : PreAcceptReplyM) {res : RState × List Out}
    (h : stepPreAcceptReply s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepPreAcceptReply] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_stepPreAcceptOK (s : RState) (m : PreAcceptOKM) {res : RState × List Out}
    (h : stepPreAcceptOK s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepPreAcceptOK] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_stepAcceptReply (s : RState) (m : AcceptReplyM) {res : RState × List Out}
    (h : stepAcceptReply s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepAcceptReply] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_stepExecuteOverwrite (s : RState) (m : ExecuteOverwriteM) {res : RState × List Out}
    (h : stepExecuteOverwrite s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepExecuteOverwrite] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_iteSc {c : Prop} [Decidable c] {s s1 : RState} {n : w32} {v : ValTag} {b : Bool}
    {o : List Out} (h : (if c then shortCircuit s n v b else some (s, [])) = some (s1, o)) :
    GhostEq s s1 := by
  split at h
  · exact ghost_shortCircuit h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact GhostEq.refl _

set_option hygiene false in
/-- A leaf after `shortCircuit`. -/
macro "gsc" : tactic => `(tactic| first
  | gall
  | (have hsc := ghost_shortCircuit ‹shortCircuit _ _ _ _ = some _›
     simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
     simp only [GhostEq] at hsc ⊢; simp [hsc]; done)
  | (have hsc := ghost_iteSc ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›
     simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
     simp only [GhostEq] at hsc ⊢; simp [hsc]; done))

theorem ghost_stepWrite1Reply (s : RState) (m : Write1ReplyM) {res : RState × List Out}
    (h : stepWrite1Reply s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepWrite1Reply] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gsc

theorem ghost_stepWrite2Reply (s : RState) (m : Write2ReplyM) {res : RState × List Out}
    (h : stepWrite2Reply s m = .ok res) : GhostEq s res.1 := by
  tsimp [stepWrite2Reply] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gsc

theorem ghost_stepRecover (s : RState) (q i : w32) {res : RState × List Out}
    (h : stepRecover s q i = .ok res) : GhostEq s res.1 := by
  tsimp [stepRecover] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_stepExec (s : RState) (q i : w32) {res : RState × List Out}
    (h : stepExec s q i = .ok res) : GhostEq s res.1 := by
  tsimp [stepExec] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals gall

theorem ghost_stepClientWrite (s : RState) (rid cid : w32) (k v : w64) (d : Dep)
    {res : RState × List Out} (h : stepClientWrite s rid cid k v d = .ok res) :
    res.1.nReqs = s.nReqs + 1 ∧ res.1.used = (cid, rid) :: s.used := by
  tsimp [stepClientWrite] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals first
    | (cases h; done)
    | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp)

theorem ghost_stepClientRead (s : RState) (rid cid : w32) (k : w64) (d : Dep)
    {res : RState × List Out} (h : stepClientRead s rid cid k d = .ok res) :
    res.1.nReqs = s.nReqs + 1 ∧ res.1.used = (cid, rid) :: s.used := by
  tsimp [stepClientRead] at h
  revert h
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · split
      · intro h; cases h
      · intro h
        obtain ⟨a, ha, hb⟩ := ex_bind_ok h
        have hI := ex_forIn_inv _ _ _ (fun b : RState => b.nReqs = s.nReqs + 1 ∧
          b.used = (cid, rid) :: s.used) ⟨rfl, rfl⟩ (by
            intro x b r hb' hr
            split at hr
            · split at hr
              · simp only [pure, Except.pure, Except.ok.injEq] at hr; subst hr; exact hb'
              · cases hr
            · simp only [pure, Except.pure, Except.ok.injEq] at hr; subst hr; exact hb') ha
        split at hb
        · simp only [pure, Except.pure, Except.ok.injEq] at hb; subst hb; exact hI
        · cases hb

theorem ghost_stepClientRMW (s : RState) (rid cid : w32) (k : w64) (d : Dep) (oldV newV : w64)
    {res : RState × List Out} (h : stepClientRMW s rid cid k d oldV newV = .ok res) :
    res.1.nReqs = s.nReqs + 1 ∧ res.1.used = (cid, rid) :: s.used := by
  tsimp [stepClientRMW] at h
  revert h
  repeat' split
  all_goals intro h
  all_goals first
    | (cases h; done)
    | (obtain ⟨-, -, h⟩ := handlePropose_ok h; unfold handleProposeBody at h
       have hg := ghost_startPhase1 _ _ _ _ _ _ h
       simp only [GhostEq] at hg
       simp [hg, RState.setCrt])

set_option maxHeartbeats 4000000 in
theorem ghost_stepPrepareReply (s : RState) (m : PrepareReplyM) {res : RState × List Out}
    (h : stepPrepareReply s m = .ok res) : GhostEq s res.1 := by
  by_cases hok1 : cmdsOk m.cmds = true
  · by_cases hbx : inBox m.replica m.inst = true
    · cases hc : s.inst m.replica m.inst with
      | none => tsimp [stepPrepareReply, hok1, hbx, hc] at h; cases h
      | some c =>
        cases hlb : c.lb with
        | none =>
          tsimp [stepPrepareReply, hok1, hbx, hc, hlb] at h
          simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact GhostEq.refl _
        | some lb0 =>
          by_cases hC : m.status = St.COMMITTED ∨ m.status = St.EXECUTED
          · tsimpd [stepPrepareReply, hok1, hbx, hc, hlb, hC] at h
            revert h
            repeat' split
            all_goals intro h
            all_goals gall
          · by_cases hA : m.status = St.ACCEPTED
            · tsimpd [stepPrepareReply, hok1, hbx, hc, hlb, hC, hA, riOf] at h
              revert h
              repeat' split
              all_goals intro h
              all_goals gall
            · by_cases hP : m.status = St.PREACCEPTED ∨ m.status = St.PREACCEPTED_EQ
              · by_cases hprep : lb0.preparing = true
                all_goals by_cases hnc0 : c.status = St.COMMITTED ∨ c.status = St.EXECUTED
                all_goals by_cases hok : m.ok = FALSE
                all_goals by_cases hbal : m.ballot = c.ballot
                all_goals rcases hri : lb0.recoveryInst with _ | ri
                all_goals by_cases hacc : m.acceptorId = m.replica
                all_goals by_cases hslt : slt (lb0.prepareOKs + 1) NHALF = true
                all_goals tsimpd [stepPrepareReply, hok1, hbx, hc, hlb, hC, hA, hP, riOf, hprep, hnc0,
                  hok, hbal, hri, hacc, hslt] at h
                all_goals revert h
                all_goals repeat' split
                all_goals intro h
                all_goals gall
              · tsimpd [stepPrepareReply, hok1, hbx, hc, hlb, hC, hA, hP, riOf] at h
                revert h
                repeat' split
                all_goals intro h
                all_goals gall
    · tsimp [stepPrepareReply, hok1, hbx] at h; cases h
  · tsimp [stepPrepareReply, hok1] at h; cases h

/-- **R-I-1** (unit I's request): a step changes the ghost fields only at a client request:
`nReqs` grows by one and `used` gains the request's key. Any state. -/
theorem stepR_ghost {k : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR k s e = .ok (s', o)) :
    s'.nReqs = s.nReqs + (if e.clientReq.isSome then 1 else 0) ∧
      ∀ key ∈ s'.used, key ∈ s.used ∨ ∃ i, e.clientReq = some (key.1, key.2, i) := by
  have hnc : GhostEq s s' → e.clientReq = none →
      s'.nReqs = s.nReqs + (if e.clientReq.isSome then 1 else 0) ∧
      ∀ key ∈ s'.used, key ∈ s.used ∨ ∃ i, e.clientReq = some (key.1, key.2, i) := by
    intro hge hn
    rw [hn]
    refine ⟨by simp [hge.1], fun key hk => Or.inl (hge.2 ▸ hk)⟩
  cases e with
  | msg m =>
    refine hnc ?_ rfl
    have hr : ∀ {res : RState × List Out}, res = (s', o) → GhostEq s res.1 → GhostEq s s' := by
      intro res he hg; subst he; exact hg
    cases m with
    | read1 m => exact hr rfl (ghost_stepRead1 s m h)
    | read2 m => exact hr rfl (ghost_stepRead2 s m h)
    | read1Reply m => exact hr rfl (ghost_stepRead1Reply s m h)
    | read2Reply m => exact hr rfl (ghost_stepRead2Reply s m h)
    | write1 m => exact hr rfl (ghost_stepWrite1 s m h)
    | write2 m => exact hr rfl (ghost_stepWrite2 s m h)
    | write1Reply m => exact hr rfl (ghost_stepWrite1Reply s m h)
    | write2Reply m => exact hr rfl (ghost_stepWrite2Reply s m h)
    | preAccept m => exact hr rfl (ghost_stepPreAccept s m h)
    | preAcceptReply m => exact hr rfl (ghost_stepPreAcceptReply s m h)
    | preAcceptOK m => exact hr rfl (ghost_stepPreAcceptOK s m h)
    | accept m => exact hr rfl (ghost_stepAccept s m h)
    | acceptReply m => exact hr rfl (ghost_stepAcceptReply s m h)
    | commit m => exact hr rfl (ghost_stepCommit s m h)
    | prepare m => exact hr rfl (ghost_stepPrepare s m h)
    | prepareReply m => exact hr rfl (ghost_stepPrepareReply s m h)
    | executed m => exact hr rfl (ghost_handleExecuted s m h)
    | executeOverwrite m => exact hr rfl (ghost_stepExecuteOverwrite s m h)
  | read rid cid k d =>
    obtain ⟨h1, h2⟩ := ghost_stepClientRead s rid cid k d h
    simp only at h1 h2
    refine ⟨by simp [Ev.clientReq, h1], fun key hk => ?_⟩
    rw [h2] at hk; simp only [List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl hk
  | write rid cid k v d =>
    obtain ⟨h1, h2⟩ := ghost_stepClientWrite s rid cid k v d h
    simp only at h1 h2
    refine ⟨by simp [Ev.clientReq, h1], fun key hk => ?_⟩
    rw [h2] at hk; simp only [List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl hk
  | rmw rid cid k d oldV newV =>
    obtain ⟨h1, h2⟩ := ghost_stepClientRMW s rid cid k d oldV newV h
    simp only at h1 h2
    refine ⟨by simp [Ev.clientReq, h1], fun key hk => ?_⟩
    rw [h2] at hk; simp only [List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl hk
  | forceWrite =>
    refine hnc ?_ rfl
    simp only [stepR, stepForceWrite, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; exact GhostEq.refl _
  | recover q i =>
    refine hnc ?_ rfl
    have := ghost_stepRecover s q i h; exact this
  | exec q i =>
    refine hnc ?_ rfl
    have := ghost_stepExec s q i h; exact this

end Perennial.gryff.pure.tot
