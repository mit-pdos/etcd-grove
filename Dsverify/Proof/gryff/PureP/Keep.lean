/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureP/Keep.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit P: a replica's step keeps its instances, and committed (COMMITTED or EXECUTED) copies stay
committed (`CKeep`); along a replica's run (`runP_ckeep`). Structural (no invariant): every handler
only adds copies, checks a committed copy's status before overwriting it (or overwrites it with a
COMMITTED one), and `handlePropose`'s slot is guarded by `slotDecided` (H2b-R2).
-/
module

public import Dsverify.Proof.gryff.PureA.Exec

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureP

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.pureA

/-- Instances are kept; committed copies stay committed. -/
def CKeep (s s' : RState) : Prop :=
  ∀ q i cp, s.inst q i = some cp → ∃ cp', s'.inst q i = some cp' ∧
    (isCommitted cp.status → isCommitted cp'.status)

theorem ck_refl (s : RState) : CKeep s s := fun _ _ cp h => ⟨cp, h, id⟩
theorem ck_inst {s t t' : RState} (h : CKeep s t) (e : t'.inst = t.inst) : CKeep s t' := by
  intro q i cp h1; rw [e]; exact h q i cp h1
theorem ck_trans {a b c : RState} (h1 : CKeep a b) (h2 : CKeep b c) : CKeep a c := by
  intro q i cp h
  obtain ⟨cp1, h3, h4⟩ := h1 q i cp h
  obtain ⟨cp2, h5, h6⟩ := h2 q i cp1 h3
  exact ⟨cp2, h5, h6 ∘ h4⟩
theorem ck_setInst {s t : RState} {q i : w32} {c : Copy} (h : CKeep s t)
    (hc : ∀ c0, t.inst q i = some c0 → isCommitted c0.status → isCommitted c.status) :
    CKeep s (t.setInst q i c) := by
  intro q' i' cp h1
  obtain ⟨cp1, h3, h4⟩ := h q' i' cp h1
  rw [setInst_inst]
  by_cases e : q' = q ∧ i' = i
  · rw [if_pos e]; obtain ⟨rfl, rfl⟩ := e; exact ⟨c, rfl, fun x => hc cp1 h3 (h4 x)⟩
  · rw [if_neg e]; exact ⟨cp1, h3, h4⟩
theorem ck_updConf {s t : RState} (h : CKeep s t) (cmds : List Cmd) (q i sq : w32) :
    CKeep s (updateConflicts t cmds q i sq) := ck_inst h (updateConflicts_inst _ _ _ _ _).1
theorem ck_updCommitted {s t t' : RState} {q : w32} (h : CKeep s t)
    (hu : updateCommitted t q = some t') : CKeep s t' := ck_inst h (updateCommitted_inst hu).1
theorem ck_proposeQ {s t : RState} (h : CKeep s t) (x : List Proposal) :
    CKeep s { t with proposeQ := x } := h
theorem ck_prevValTag {s t : RState} (h : CKeep s t) (x : Option ValTag) :
    CKeep s { t with prevValTag := x } := h
theorem ck_setCrt {s t : RState} (h : CKeep s t) (q x : w32) : CKeep s (t.setCrt q x) := h
theorem ck_frame {s t : RState} (h : Frame s t) : CKeep s t := ck_inst (ck_refl s) h.2.1

theorem isC_C : isCommitted St.COMMITTED := Or.inl rfl
theorem isC_E : isCommitted St.EXECUTED := Or.inr rfl
theorem ncom3 {x : w8} (hn : ¬(x = St.COMMITTED ∨ x = St.ACCEPTED ∨ x = St.EXECUTED))
    (h : isCommitted x) : False := by
  rcases h with h | h <;> exact hn (by simp [h])
theorem nofalse {o : Option Copy} {c0 : Copy} (h : ∀ c, o = some c → False) (h0 : o = some c0) :
    False := h c0 h0
theorem ncom2 {x : w8} (hn : ¬(x = St.COMMITTED ∨ x = St.EXECUTED)) (h : isCommitted x) : False :=
  hn h

set_option maxRecDepth 20000

macro "ck_side" : tactic => `(tactic| (
  intro c0 hc0 hcom
  try simp only [setCrt_inst', setInst_inst, (updateConflicts_inst _ _ _ _ _).1] at hc0
  first
    | exact isC_C
    | exact isC_E
    | exact hcom
    | exact (nofalse (by assumption) hc0).elim
    | (simp only [eq_self_iff_true, and_self, ↓reduceIte, Option.some.injEq] at hc0
       subst hc0
       first
         | exact hcom
         | exact (ncom3 (by assumption) hcom).elim
         | exact (ncom2 (by assumption) hcom).elim
         | (simp_all [isCommitted, St.COMMITTED, St.EXECUTED, St.ACCEPTED, St.PREACCEPTED,
             St.PREACCEPTED_EQ, St.NONE]; done))
    | (simp only [hc0, Option.some.injEq] at *; subst_vars
       first
         | exact hcom
         | exact (ncom3 (by assumption) hcom).elim
         | exact (ncom2 (by assumption) hcom).elim
         | (simp_all [isCommitted, St.COMMITTED, St.EXECUTED, St.ACCEPTED, St.PREACCEPTED,
             St.PREACCEPTED_EQ, St.NONE]; done))
    | (simp_all [isCommitted, St.COMMITTED, St.EXECUTED, St.ACCEPTED, St.PREACCEPTED,
             St.PREACCEPTED_EQ, St.NONE]; done)))

macro "ck_fin" : tactic => `(tactic| (
  repeat (first
    | exact ck_refl _
    | (apply ck_updCommitted ?_ ‹updateCommitted _ _ = some _›)
    | apply ck_updConf
    | apply ck_setInst
    | apply ck_proposeQ
    | apply ck_prevValTag
    | apply ck_setCrt)
  all_goals ck_side))

theorem stepCommit_ck {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) : CKeep s s' := by
  unfold stepCommit at h; peel h
  all_goals (cases h; ck_fin)

theorem leaderCommit_ck {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit s q i c lb = .ok (s', o)) : CKeep s s' := by
  unfold leaderCommit at h; peel h
  all_goals (cases h; ck_fin)

theorem startPhase1_ck {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o))
    (hn : ∀ c0, s.inst q i = some c0 → ¬ isCommitted c0.status) : CKeep s s' := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; ck_fin)
  all_goals (exact absurd hcom (hn _ hc0))

macro "ck_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; ck_fin; done)
    | (refine ck_trans ?_ (leaderCommit_ck $h:ident); ck_fin; done)
    | (refine ck_trans ?_ (startPhase1_ck $h:ident ?_); ck_fin; done)
    | skip)))

set_option maxRecDepth 200000 in
theorem stepPreAccept_ck {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) : CKeep s s' := by
  unfold stepPreAccept at h; ck_close h
theorem stepAccept_ck {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) : CKeep s s' := by
  unfold stepAccept at h; ck_close h
theorem stepPreAcceptReply_ck {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) : CKeep s s' := by
  unfold stepPreAcceptReply at h; ck_close h
theorem stepPreAcceptOK_ck {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) : CKeep s s' := by
  unfold stepPreAcceptOK at h; ck_close h
theorem stepAcceptReply_ck {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) : CKeep s s' := by
  unfold stepAcceptReply at h; ck_close h
theorem stepPrepare_ck {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) : CKeep s s' := by
  unfold stepPrepare at h; ck_close h
theorem stepPrepareReply_ck {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) : CKeep s s' := by
  unfold stepPrepareReply at h; ck_close h
theorem handleExecuted_ck {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) : CKeep s s' := by
  unfold handleExecuted at h; ck_close h
theorem stepRecover_ck {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) : CKeep s s' := by
  unfold stepRecover at h; ck_close h
theorem stepExec_ck {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) : CKeep s s' := by
  unfold stepExec at h; ck_close h

theorem notDecided {s : RState} {q i : w32} (h : slotDecided s q i = false) :
    ∀ c0, s.inst q i = some c0 → ¬ isCommitted c0.status := by
  intro c0 hc hcom
  unfold slotDecided at h; rw [hc] at h
  rcases hcom with e | e <;> simp [e] at h

theorem handlePropose_ck {s s' : RState} {p : Proposal} {o : List Out}
    (h : handlePropose s p = .ok (s', o)) : CKeep s s' := by
  obtain ⟨-, hd, h⟩ := handlePropose_ok h
  unfold handleProposeBody at h
  exact ck_trans (ck_proposeQ (ck_setCrt (ck_refl s) _ _) _) (startPhase1_ck h (notDecided hd))

theorem stepClientRMW_ck {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    {o : List Out} (h : stepClientRMW s rid cid k d a b = .ok (s', o)) : CKeep s s' := by
  unfold stepClientRMW at h; peel h
  exact handlePropose_ck (s := { s with nReqs := s.nReqs + 1, used := (cid, rid) :: s.used }) h

theorem stepExecuteOverwrite_ck {s s' : RState} {m : ExecuteOverwriteM} {o : List Out}
    (h : stepExecuteOverwrite s m = .ok (s', o)) : CKeep s s' := by
  have hs : CKeep s (s.overwrite m.v m.t) := ck_frame (overwrite_frame s m.v m.t)
  unfold stepExecuteOverwrite at h; peel h
  · exact ck_trans hs (handleExecuted_ck h)
  · cases h; exact hs

/-- **Every step** keeps the instances and the committed copies. -/
theorem step_ck {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) : CKeep s s' := by
  cases e with
  | read => exact ck_frame (stepClientRead_frame h)
  | write => exact ck_frame (stepClientWrite_frame h)
  | rmw => exact stepClientRMW_ck h
  | forceWrite => cases h; exact ck_refl _
  | recover => exact stepRecover_ck h
  | exec => exact stepExec_ck h
  | msg m =>
    cases m with
    | read1 => exact ck_frame (stepRead1_frame h)
    | read2 => exact ck_frame (stepRead2_frame h)
    | write1 => exact ck_frame (stepWrite1_frame h)
    | write2 => exact ck_frame (stepWrite2_frame h)
    | read1Reply => exact ck_frame (stepRead1Reply_frame h)
    | read2Reply => exact ck_frame (stepRead2Reply_frame h)
    | write1Reply => exact ck_frame (stepWrite1Reply_frame h)
    | write2Reply => exact ck_frame (stepWrite2Reply_frame h)
    | prepare => exact stepPrepare_ck h
    | preAccept => exact stepPreAccept_ck h
    | accept => exact stepAccept_ck h
    | commit => exact stepCommit_ck h
    | prepareReply => exact stepPrepareReply_ck h
    | preAcceptReply => exact stepPreAcceptReply_ck h
    | preAcceptOK => exact stepPreAcceptOK_ck h
    | acceptReply => exact stepAcceptReply_ck h
    | executed => exact handleExecuted_ck h
    | executeOverwrite => exact stepExecuteOverwrite_ck h

/-- Along a replica's run: from the state after a prefix to the state after the whole run. -/
theorem runP_ckeep {r : Fin 3} {es : List Ev} {s : RState} {o : List Out}
    (h : kahn.runP gNet r es = some (s, o)) {j k : Nat} (hjk : j ≤ k) (hk : k ≤ es.length) :
    CKeep (stOf r (es.take j)) (stOf r (es.take k)) := by
  induction k with
  | zero => have : j = 0 := by omega
            subst this; exact ck_refl _
  | succ k ih =>
    by_cases e : j = k + 1
    · subst e; exact ck_refl _
    have hk' : k < es.length := by omega
    obtain ⟨o', hs⟩ := runP_step h (List.getElem?_eq_getElem hk')
    exact ck_trans (ih (by omega) (by omega)) (step_ck hs)

end Perennial.gryff.pureP
