/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/Heads.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b (RMW side): **head proposals stay at their instance** (`HFlow s s'`): the first
proposal of an instance's bookkeeping in `s'` was the first proposal of the same instance's
bookkeeping in `s` — for every handler but `handlePropose`, which puts the new proposal first at
the new instance (`startPhase1_head`).
-/
module

public import Dsverify.Proof.gryff.PureLb.RmwOwn
public import Dsverify.Proof.gryff.PureLb.WPlace

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-- `p` is the first proposal of instance `(q, i)`'s bookkeeping in `s`. -/
def HeadIn (s : RState) (q i : w32) (p : Proposal) : Prop :=
  ∃ c lb, s.inst q i = some c ∧ c.lb = some lb ∧ lb.clientProposals.head? = some p

def HFlow (s s' : RState) : Prop := ∀ q i p, HeadIn s' q i p → HeadIn s q i p

/-- Copy `c` at `(q, i)` has `s`'s head there. -/
def CH (s : RState) (q i : w32) (c : Copy) : Prop :=
  ∀ lb p, c.lb = some lb → lb.clientProposals.head? = some p → HeadIn s q i p

/-- A proposal list whose head is `s`'s head at `(q, i)`. -/
def LBH (s : RState) (q i : w32) (L : List Proposal) : Prop :=
  ∀ p, L.head? = some p → HeadIn s q i p

theorem HFlow.rfl' (s : RState) : HFlow s s := fun _ _ _ h => h

theorem hflow_setInst {s X : RState} (h : HFlow s X) {q i : w32} {c : Copy} (hc : CH s q i c) :
    HFlow s (X.setInst q i c) := by
  intro q' i' p ⟨c', lb, hc', hlb, hp⟩
  change (if q' = q ∧ i' = i then some c else X.inst q' i') = some c' at hc'
  split at hc'
  · rename_i hqi; obtain ⟨rfl, rfl⟩ := hqi
    cases hc'; exact hc lb p hlb hp
  · exact h q' i' p ⟨c', lb, hc', hlb, hp⟩

theorem hflow_same {s X X' : RState} (h : HFlow s X) (h1 : X'.inst = X.inst) : HFlow s X' := by
  intro q i p ⟨c', lb, hc', hlb, hp⟩
  rw [h1] at hc'; exact h q i p ⟨c', lb, hc', hlb, hp⟩

theorem hflow_updC {s X : RState} (h : HFlow s X) (cmds : List Cmd) (q i sq : w32) :
    HFlow s (updateConflicts X cmds q i sq) := hflow_same h (updateConflicts_inst' X cmds q i sq).1

theorem hflow_overwrite {s X : RState} (h : HFlow s X) (v : w64) (t : model.Tag) :
    HFlow s (X.overwrite v t) := hflow_same h (tot.ow_inst ..)

theorem hflow_setCrt {s X : RState} (h : HFlow s X) (q x : w32) : HFlow s (X.setCrt q x) :=
  hflow_same h rfl

theorem hflow_updCommitted' {s X X' : RState} (h : HFlow s X) {q : w32}
    (hu : updateCommitted X q = some X') : HFlow s X' := by
  obtain ⟨cu, rfl⟩ := tot.updateCommitted_form hu
  exact hflow_same h rfl

theorem ch_none {s : RState} {q i : w32} {c : Copy} (h : c.lb = none) : CH s q i c := by
  intro lb p hlb; rw [h] at hlb; cases hlb

theorem EqIP.hf {s s' : RState} (h : EqIP s s') : HFlow s s' := hflow_same (HFlow.rfl' s) h.1

macro "hf_fin" : tactic => `(tactic| (
  repeat' (first
    | with_reducible exact HFlow.rfl' _
    | with_reducible assumption
    | (guard_target =~ HFlow _ _
       first
       | with_reducible apply hflow_setInst
       | with_reducible apply hflow_updC
       | with_reducible apply hflow_overwrite
       | with_reducible apply hflow_setCrt
       | (obtain ⟨_, rfl⟩ := tot.updateCommitted_form ‹model.updateCommitted _ _ = some _›)
       | (guard_target =~ HFlow _ (RState.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
          with_reducible apply hflow_same (X := _) _ (by with_reducible rfl)))
    | (guard_target =~ CH _ _ _ _
       first
       | exact ch_none rfl
       | (intro lb p hlb hp
          first
          | (cases hlb; done)
          | (simp only [Option.some.injEq] at hlb; subst hlb
             first
             | exact ⟨_, _, by assumption, by assumption, by exact hp⟩
             | exact (by assumption : LBH _ _ _ _) p (by exact hp))
          | (simp only at hlb
             exact ⟨_, _, by assumption, hlb, hp⟩)))
    | (guard_target =~ LBH _ _ _ _
       intro p hp
       exact ⟨_, _, by assumption, by assumption, by exact hp⟩))))

/-- `startPhase1` puts `ps` at `(q, i)` and keeps every other instance. -/
theorem startPhase1_head {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o)) :
    ∀ q' i' p, HeadIn s' q' i' p → ((q' = q ∧ i' = i) ∧ ps.head? = some p) ∨
      (¬(q' = q ∧ i' = i) ∧ HeadIn s q' i' p) := by
  unfold startPhase1 at h; peel h
  all_goals (cases h)
  all_goals (intro q' i' p ⟨c', lb, hc', hlb, hp⟩
             rw [(updateConflicts_inst' _ _ _ _ _).1] at hc'
             change (if q' = q ∧ i' = i then some _ else s.inst q' i') = some c' at hc'
             split at hc'
             · rename_i hqi; cases hc'; simp only [Option.some.injEq] at hlb; subst hlb
               exact Or.inl ⟨hqi, hp⟩
             · rename_i hqi; exact Or.inr ⟨hqi, c', lb, hc', hlb, hp⟩)

theorem startPhase1_hf {s0 s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (hX : HFlow s0 s) (hps : LBH s0 q i ps)
    (h : startPhase1 s q i b ps cs = .ok (s', o)) : HFlow s0 s' := by
  intro q' i' p hp
  rcases startPhase1_head h q' i' p hp with ⟨⟨rfl, rfl⟩, h1⟩ | ⟨-, h1⟩
  · exact hps p h1
  · exact hX q' i' p h1

theorem leaderCommit_hf {s0 s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (hX : HFlow s0 s) (hps : LBH s0 q i lb.clientProposals)
    (h : leaderCommit s q i c lb = .ok (s', o)) : HFlow s0 s' := by
  have hc1 : CH s0 q i { c with status := St.COMMITTED, lb := some lb } := by
    intro lb' p hlb hp
    simp only [Option.some.injEq] at hlb; subst hlb; exact hps p hp
  unfold leaderCommit at h; peel h
  all_goals (cases h)
  · rename_i _ s1 hu _ _ _
    refine hflow_setInst ?_ (ch_none rfl)
    exact hflow_same (hflow_updCommitted' (hflow_setInst hX hc1) hu) rfl
  · first
    | (rename_i hu _ _; exact hflow_updCommitted' (hflow_setInst hX hc1) hu)
    | (rename_i hu _ _ _ _; exact hflow_updCommitted' (hflow_setInst hX hc1) hu)
    | (rename_i hu _; exact hflow_updCommitted' (hflow_setInst hX hc1) hu)
    | (rename_i hu; exact hflow_updCommitted' (hflow_setInst hX hc1) hu)

theorem ch_same {s X : RState} (h : HFlow s X) {q i : w32} {c0 : Copy}
    (hc : X.inst q i = some c0) {c : Copy} (hlb : c.lb = c0.lb) : CH s q i c := by
  intro lb p h1 hp
  rw [hlb] at h1
  exact h q i p ⟨c0, lb, hc, h1, hp⟩

macro "hf_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; hf_fin; done)
    | (refine leaderCommit_hf ?_ ?_ $h:ident <;> hf_fin; done)
    | (refine startPhase1_hf ?_ ?_ $h:ident <;> hf_fin; done))))

theorem handleExecuted_hf {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) : HFlow s s' := by
  unfold handleExecuted at h; peel h
  all_goals (cases h; hf_fin)

theorem stepPreAccept_hf {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) : HFlow s s' := by
  unfold stepPreAccept at h; peel h
  all_goals (cases h; hf_fin)

theorem stepPreAcceptReply_hf {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) : HFlow s s' := by
  unfold stepPreAcceptReply at h; peel h
  all_goals (first | (cases h; hf_fin; done) | skip)
  all_goals (refine leaderCommit_hf ?_ ?_ h <;> hf_fin)

theorem stepPreAcceptOK_hf {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) : HFlow s s' := by
  unfold stepPreAcceptOK at h; hf_close h

theorem stepAccept_hf {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) : HFlow s s' := by
  unfold stepAccept at h; hf_close h

theorem stepAcceptReply_hf {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) : HFlow s s' := by
  unfold stepAcceptReply at h; hf_close h

theorem stepCommit_hf {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) : HFlow s s' := by
  unfold stepCommit at h; peel h
  all_goals (cases h)
  all_goals (first | exact HFlow.rfl' _ | exact hflow_setCrt (HFlow.rfl' _) _ _ | skip)
  all_goals (refine hflow_updCommitted' ?_ ‹model.updateCommitted _ _ = some _›)
  all_goals (first | refine hflow_updC ?_ _ _ _ _ | skip)
  all_goals (refine hflow_setInst ?_ ?_)
  all_goals (first
    | exact HFlow.rfl' _
    | exact hflow_setCrt (HFlow.rfl' _) _ _
    | exact hflow_same (X := s) (HFlow.rfl' _) rfl
    | exact hflow_same (X := s.setCrt m.replica (m.inst + 1)) (hflow_setCrt (HFlow.rfl' _) _ _) rfl
    | exact ch_none rfl
    | exact ch_same (HFlow.rfl' _) (c0 := ‹Copy›) (by assumption) rfl)

theorem stepPrepare_hf {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) : HFlow s s' := by
  unfold stepPrepare at h; peel h
  all_goals (cases h; refine hflow_setInst (HFlow.rfl' _) ?_)
  all_goals (first
    | exact ch_none rfl
    | (refine ch_same (HFlow.rfl' _) (by assumption) ?_; split <;> rfl)
    | (refine ch_same (HFlow.rfl' _) (by assumption) ?_; rfl))

theorem stepPrepareReply_hf {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) : HFlow s s' := by
  unfold stepPrepareReply at h; hf_close h

theorem stepRecover_hf {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) : HFlow s s' := by
  unfold stepRecover at h; peel h
  all_goals (cases h)
  all_goals (first | exact HFlow.rfl' _ | refine hflow_setInst (HFlow.rfl' _) ?_)
  all_goals (intro lb p hlb; simp only [Option.some.injEq] at hlb; subst hlb; dsimp only)
  all_goals (first | (split <;> intro hp) | intro hp)
  all_goals (first
    | (cases hp; done)
    | exact ⟨_, _, by assumption, by assumption, hp⟩)

theorem stepExec_hf {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) : HFlow s s' := by
  unfold stepExec at h; peel h
  all_goals (cases h)
  all_goals (refine hflow_setInst ?_ (ch_same (HFlow.rfl' _) (c0 := ‹Copy›) (by assumption) rfl))
  all_goals (first | exact HFlow.rfl' _ | exact hflow_same (HFlow.rfl' _) rfl)

theorem stepExecuteOverwrite_hf {s s' : RState} {m : ExecuteOverwriteM} {o : List Out}
    (h : stepExecuteOverwrite s m = .ok (s', o)) : HFlow s s' := by
  unfold stepExecuteOverwrite at h; peel h
  all_goals (first
    | (cases h; exact hflow_overwrite (HFlow.rfl' _) _ _)
    | exact fun q i p hp => hflow_overwrite (HFlow.rfl' s) m.v m.t q i p (handleExecuted_hf h q i p hp))

/-- A client RMW's new instance `(s.id, crt)` has its proposal first. -/
theorem stepClientRMW_head {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    {o : List Out} (h : stepClientRMW s rid cid k d a b = .ok (s', o)) :
    ∀ q i p, HeadIn s' q i p → (q = s.id ∧ i = s.crt s.id ∧ p.client = cid ∧ p.cmdId = rid) ∨
      HeadIn s q i p := by
  unfold stepClientRMW at h
  peel h
  replace h := (handlePropose_ok h).2.2; unfold handleProposeBody at h
  intro q i p hp
  rcases startPhase1_head h q i p hp with ⟨⟨rfl, rfl⟩, h1⟩ | ⟨-, h1⟩
  · simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inr h1

theorem step_hflow {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) :
    ∀ q i p, HeadIn s' q i p → HeadIn s q i p ∨ ∃ rid cid k d a b, e = .rmw rid cid k d a b ∧
      q = s.id ∧ i = s.crt s.id ∧ p.client = cid ∧ p.cmdId = rid := by
  have L : HFlow s s' → ∀ q i p, HeadIn s' q i p → HeadIn s q i p ∨ ∃ rid cid k d a b,
      e = .rmw rid cid k d a b ∧ q = s.id ∧ i = s.crt s.id ∧ p.client = cid ∧ p.cmdId = rid :=
    fun hf q i p hp => Or.inl (hf q i p hp)
  cases e with
  | read => exact L (stepClientRead_eqip h).hf
  | write => exact L (stepClientWrite_eqip h).hf
  | rmw rid cid k d a b =>
    intro q i p hp
    rcases stepClientRMW_head h q i p hp with ⟨h1, h2, h3, h4⟩ | h1
    · exact Or.inr ⟨rid, cid, k, d, a, b, rfl, h1, h2, h3, h4⟩
    · exact Or.inl h1
  | forceWrite => cases h; exact L (HFlow.rfl' _)
  | recover => exact L (stepRecover_hf h)
  | exec => exact L (stepExec_hf h)
  | msg m =>
    cases m with
    | read1 => exact L (stepRead1_eqip h).hf
    | read2 => exact L (stepRead2_eqip h).hf
    | write1 => exact L (stepWrite1_eqip h).hf
    | write2 => exact L (stepWrite2_eqip h).hf
    | read1Reply => exact L (stepRead1Reply_eqip h).hf
    | read2Reply => exact L (stepRead2Reply_eqip h).hf
    | write1Reply => exact L (stepWrite1Reply_eqip h).hf
    | write2Reply => exact L (stepWrite2Reply_eqip h).hf
    | prepare => exact L (stepPrepare_hf h)
    | preAccept => exact L (stepPreAccept_hf h)
    | accept => exact L (stepAccept_hf h)
    | commit => exact L (stepCommit_hf h)
    | prepareReply => exact L (stepPrepareReply_hf h)
    | preAcceptReply => exact L (stepPreAcceptReply_hf h)
    | preAcceptOK => exact L (stepPreAcceptOK_hf h)
    | acceptReply => exact L (stepAcceptReply_hf h)
    | executed => exact L (handleExecuted_hf h)
    | executeOverwrite => exact L (stepExecuteOverwrite_hf h)

/-! ## The head invariant -/

theorem rmwInst_snoc {l : List Label} {o : Op} (ho : o ∈ ops l) (x : Label) :
    rmwInst (l ++ [x]) o = rmwInst l o := by
  obtain ⟨i, e⟩ := x
  unfold rmwInst
  rw [proj_snoc]
  split
  · rw [List.take_append_of_le_length (op_j_le ho)]
  · rfl

/-- **An instance's head proposal is the RMW whose request created the instance.** -/
def HOwn (l : List Label) (c : Cfg gNet) : Prop :=
  ∀ R q i p, HeadIn (stR c R) q i p → ∃ o ∈ ops l, o.r = R ∧ (∃ a b, o.inp = .cas a b) ∧
    o.cid = p.client ∧ o.rid = p.cmdId ∧ rmwInst l o = (q, i)

theorem hown_init : HOwn [] (Cfg.init gNet) := by
  rintro R q i p ⟨c, lb, hc, -⟩
  change (RState.init R.val).inst q i = some c at hc
  cases hc

theorem hown_step {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {x : List Ext}
    (h : GRun (Cfg.init gNet) l c) (hi : HOwn l c) (hst : GStep c i e c' x) :
    HOwn (l ++ [(i, e)]) c' := by
  obtain ⟨s', o, hs⟩ := StepAt.of h hst
  have hW := winv h
  have hmono : ∀ o ∈ ops l, o ∈ ops (l ++ [(i, e)]) := fun o ho => by
    rw [ops_snoc]; exact List.mem_append_left _ ho
  intro R q j p hp
  by_cases hR : R = i
  · subst hR
    rw [hs.sti] at hp
    rcases step_hflow hs.ok q j p hp with h1 | ⟨rid, cid, k, d, a, b, rfl, h2, h3, h4, h5⟩
    · obtain ⟨o', ho', a1, a2, a3, a4, a5⟩ := hi R q j p h1
      exact ⟨o', hmono o' ho', a1, a2, a3, a4, by rw [rmwInst_snoc ho']; exact a5⟩
    · rw [ops_snoc_req (l := l) (i := R) (e := .rmw rid cid k d a b) rfl]
      refine ⟨_, List.mem_append_right _ (List.mem_singleton.2 rfl), rfl, ⟨a, b, rfl⟩,
        h4.symm, h5.symm, ?_⟩
      have hid : (stR c R).id = rid32 R := hW.1.id R
      have hst : stOf R (projR l R) = stR c R := by
        have := cutSt_len h R
        unfold cutSt at this; rwa [List.take_length] at this
      unfold rmwInst
      simp only
      rw [proj_snoc, if_pos rfl, List.take_append_of_le_length (Nat.le_refl _), List.take_length,
        hst, h2, h3, hid]
  · rw [hs.stj hR] at hp
    obtain ⟨o', ho', a1, a2, a3, a4, a5⟩ := hi R q j p hp
    exact ⟨o', hmono o' ho', a1, a2, a3, a4, by rw [rmwInst_snoc ho']; exact a5⟩

/-- **The head invariant holds along every run.** -/
theorem hown {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) : HOwn l c :=
  grun_inv HOwn hown_init (fun _ _ _ _ _ _ h hi hs => hown_step h hi hs) l c h

end Perennial.gryff.pure
