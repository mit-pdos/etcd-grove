/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureL/StoreSteps.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L: **a step never lowers the store** (`step_tag_mono`): a lemma per handler (`*_tg`), each by
peeling the handler's `do` block (`PureL/Peel.lean`); the store changes only through
`RState.overwrite`, and the loops (`updateConflicts`, `shortCircuit`, `stepClientRead`'s) keep it.
-/
module

public import Dsverify.Proof.gryff.Pure.LinDefs
public import Dsverify.Proof.gryff.PureL.Peel
public import Dsverify.Proof.gryff.Proto.TagOrder

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

theorem forIn_id_inv {α β : Type} (l : List α) (b : β) (f : α → β → Id (ForInStep β))
    (P : β → Prop) (h0 : P b) (hf : ∀ a b, P b → P (f a b).run.value) : P (forIn l b f).run := by
  induction l generalizing b with
  | nil => exact h0
  | cons a l ih =>
    rw [List.forIn_cons]
    have := hf a b h0
    cases hfa : f a b with
    | done b' => rw [hfa] at this; exact this
    | yield b' => rw [hfa] at this; exact ih b' this

theorem forIn_opt_inv {α β : Type} (l : List α) (b : β) (f : α → β → Option (ForInStep β))
    (P : β → Prop) (h0 : P b) (hf : ∀ a b st, P b → f a b = some st → P st.value) :
    ∀ r, forIn l b f = some r → P r := by
  induction l generalizing b with
  | nil => intro r h; cases h; exact h0
  | cons a l ih =>
    intro r h
    rw [List.forIn_cons] at h
    cases hfa : f a b with
    | none => rw [hfa] at h; cases h
    | some st =>
      have := hf a b st h0 hfa
      rw [hfa] at h
      cases st with
      | done b' => cases h; exact this
      | yield b' => exact ih b' this r h

theorem forIn_exc_inv {ε α β : Type} (l : List α) (b : β) (f : α → β → Except ε (ForInStep β))
    (P : β → Prop) (h0 : P b) (hf : ∀ a b st, P b → f a b = .ok st → P st.value) :
    ∀ r, forIn l b f = .ok r → P r := by
  induction l generalizing b with
  | nil => intro r h; cases h; exact h0
  | cons a l ih =>
    intro r h
    rw [List.forIn_cons] at h
    cases hfa : f a b with
    | error e => rw [hfa] at h; cases h
    | ok st =>
      have := hf a b st h0 hfa
      rw [hfa] at h
      cases st with
      | done b' => cases h; exact this
      | yield b' => exact ih b' this r h

theorem updateConflicts_tag (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).tag = s.tag ∧ (updateConflicts s cmds q i sq).val = s.val := by
  unfold updateConflicts
  apply forIn_id_inv (P := fun x : RState => x.tag = s.tag ∧ x.val = s.val) _ _ _ ⟨rfl, rfl⟩
  intro a b hb
  simpa using hb

theorem Tag.lt_iff (a b : model.Tag) : Iff (a.lt b = true) (tagLt a.toP b.toP) := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp only [model.Tag.lt, model.Tag.cmp, model.Tag.toP, tagLt, slt]
  have e1 : (a1 == b1) = decide (sint.Z a1 = sint.Z b1) := by
    unfold sint.Z; by_cases h : a1 = b1 <;> simp [h, BitVec.toInt_inj]
  have e2 : (a2 == b2) = decide (sint.Z a2 = sint.Z b2) := by
    unfold sint.Z; by_cases h : a2 = b2 <;> simp [h, BitVec.toInt_inj]
  have e3 : (a3 == b3) = decide (sint.Z a3 = sint.Z b3) := by
    unfold sint.Z; by_cases h : a3 = b3 <;> simp [h, BitVec.toInt_inj]
  simp only [e1, e2, e3]
  generalize sint.Z a1 = x1 at *; generalize sint.Z a2 = x2 at *; generalize sint.Z a3 = x3 at *
  generalize sint.Z b1 = y1 at *; generalize sint.Z b2 = y2 at *; generalize sint.Z b3 = y3 at *
  split <;> rename_i h1 <;> (try split) <;> simp_all <;> omega

theorem overwrite_tag (s : RState) (v : w64) (t : model.Tag) :
    tagLe s.tag.toP (s.overwrite v t).tag.toP ∧ tagLe t.toP (s.overwrite v t).tag.toP := by
  unfold RState.overwrite
  by_cases h : s.tag.lt t = true
  · simp only [h, if_true]; exact ⟨Or.inl ((Tag.lt_iff _ _).1 h), tagLe_refl _⟩
  · simp only [h]
    refine ⟨tagLe_refl _, ?_⟩
    rw [← not_tagLt_iff]; intro h'; exact h ((Tag.lt_iff _ _).2 h')

def TG (s s' : RState) : Prop := tagLe s.tag.toP s'.tag.toP
theorem TG.refl' {s s' : RState} (h : s'.tag = s.tag) : TG s s' := by unfold TG; rw [h]; exact tagLe_refl _
theorem TG.trans' {a b c : RState} (h1 : TG a b) (h2 : TG b c) : TG a c := tagLe_trans h1 h2

theorem overwrite_tag_eq (s : RState) (v : w64) (t : model.Tag) :
    (s.overwrite v t).tag = if s.tag.lt t = true then t else s.tag := by
  unfold RState.overwrite; split <;> rfl
theorem setInst_tag (s : RState) (q i : w32) (c : Copy) : (s.setInst q i c).tag = s.tag := rfl
theorem setCrt_tag (s : RState) (q x : w32) : (s.setCrt q x).tag = s.tag := rfl

theorem updateCommitted_tag {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    s'.tag = s.tag := by
  unfold updateCommitted at h; opeel h
  all_goals (cases h; rfl)

theorem shortCircuit_tag {s s' : RState} {n : w32} {v : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n v f = some (s', o)) : s'.tag = s.tag := by
  rcases Perennial.gryff.model.shortCircuit_cases h with h | ⟨rfl, rfl⟩
  rotate_left
  · rfl
  unfold Perennial.gryff.model.shortCircuitReads at h
  opeel h
  all_goals
    cases h
    refine forIn_opt_inv _ _ _ (fun p : RState × List Out => p.1.tag = s.tag) rfl ?_ _ ‹_›
    intro a b st hb hf
    opeel hf
    all_goals (cases hf; simpa using hb)

theorem shortCircuit_ite_tag {s s' : RState} {c : Prop} [Decidable c] {n : w32} {v : ValTag}
    {f : Bool} {o : List Out}
    (h : (if c then shortCircuit s n v f else some (s, [])) = some (s', o)) : s'.tag = s.tag := by
  split at h
  · exact shortCircuit_tag h
  · cases h; rfl

macro "tg_fin" : tactic => `(tactic| (
  unfold TG
  try (have hu := updateCommitted_tag ‹updateCommitted _ _ = some _›; simp only [hu] at *)
  try (have hsc := shortCircuit_tag ‹shortCircuit _ _ _ _ = some _›; simp only [hsc] at *)
  try (have hsc := shortCircuit_ite_tag ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›;
       simp only [hsc] at *)
  try simp only [overwrite_tag_eq, setInst_tag, setCrt_tag, (updateConflicts_tag _ _ _ _ _).1] at *
  try (have hu := updateCommitted_tag ‹updateCommitted _ _ = some _›; simp only [hu] at *)
  try (have hsc := shortCircuit_tag ‹shortCircuit _ _ _ _ = some _›; simp only [hsc] at *)
  repeat' split
  all_goals (try simp only [Tag.lt_iff, Bool.not_eq_true] at *)
  all_goals (first | exact tagLe_refl _ | (simp only [tagLe, tagLt, Tag.toP, Prod.mk.injEq] at *; omega))))

theorem startPhase1_tg {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o)) : TG s s' := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; tg_fin)

theorem leaderCommit_tg {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit s q i c lb = .ok (s', o)) : TG s s' := by
  unfold leaderCommit at h; peel h
  all_goals (cases h; tg_fin)

macro "tg_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; tg_fin; done)
    | (refine TG.trans' ?_ (leaderCommit_tg $h:ident); tg_fin; done)
    | (refine TG.trans' ?_ (startPhase1_tg $h:ident); tg_fin; done))))

theorem handleExecuted_tg {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) : TG s s' := by
  unfold handleExecuted at h; tg_close h

theorem stepRead1Reply_tg {s s' : RState} {m : Read1ReplyM} {o : List Out}
    (h : stepRead1Reply s m = .ok (s', o)) : TG s s' := by
  unfold stepRead1Reply at h; tg_close h

theorem stepRead2Reply_tg {s s' : RState} {m : Read2ReplyM} {o : List Out}
    (h : stepRead2Reply s m = .ok (s', o)) : TG s s' := by
  unfold stepRead2Reply at h; tg_close h

theorem stepWrite1Reply_tg {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) : TG s s' := by
  unfold stepWrite1Reply at h; tg_close h

theorem stepWrite2Reply_tg {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (h : stepWrite2Reply s m = .ok (s', o)) : TG s s' := by
  unfold stepWrite2Reply at h; tg_close h

theorem stepPreAccept_tg {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) : TG s s' := by
  unfold stepPreAccept at h; tg_close h

theorem stepPreAcceptReply_tg {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) : TG s s' := by
  unfold stepPreAcceptReply at h; tg_close h

theorem stepPreAcceptOK_tg {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) : TG s s' := by
  unfold stepPreAcceptOK at h; tg_close h

theorem stepAccept_tg {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) : TG s s' := by
  unfold stepAccept at h; tg_close h

theorem stepAcceptReply_tg {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) : TG s s' := by
  unfold stepAcceptReply at h; tg_close h

theorem stepCommit_tg {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) : TG s s' := by
  unfold stepCommit at h; tg_close h

theorem stepPrepare_tg {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) : TG s s' := by
  unfold stepPrepare at h; tg_close h

theorem stepPrepareReply_tg {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) : TG s s' := by
  unfold stepPrepareReply at h; tg_close h

theorem stepClientWrite_tg {s s' : RState} {rid cid : w32} {k v : w64} {d : Dep} {o : List Out}
    (h : stepClientWrite s rid cid k v d = .ok (s', o)) : TG s s' := by
  unfold stepClientWrite at h; tg_close h

theorem stepClientRMW_tg {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    {o : List Out} (h : stepClientRMW s rid cid k d a b = .ok (s', o)) : TG s s' := by
  unfold stepClientRMW at h; peel h
  all_goals (obtain ⟨-, -, h⟩ := handlePropose_ok h; unfold handleProposeBody at h; refine TG.trans' ?_ (startPhase1_tg h); tg_fin)

theorem stepRecover_tg {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) : TG s s' := by
  unfold stepRecover at h; tg_close h

theorem stepExec_tg {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) : TG s s' := by
  unfold stepExec at h; tg_close h

theorem stepExecuteOverwrite_tg {s s' : RState} {m : ExecuteOverwriteM} {o : List Out}
    (h : stepExecuteOverwrite s m = .ok (s', o)) : TG s s' := by
  unfold stepExecuteOverwrite at h
  peel h
  all_goals (first
    | (cases h; tg_fin; done)
    | (refine TG.trans' ?_ (handleExecuted_tg h); tg_fin; done))

theorem stepClientRead_tg {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {o : List Out}
    (h : stepClientRead s rid cid k d = .ok (s', o)) : TG s s' := by
  unfold stepClientRead at h
  peel h
  cases h
  apply TG.refl'
  have hx := ‹forIn _ _ _ = Except.ok s'›
  refine forIn_exc_inv _ _ _ (fun x : RState => x.tag = s.tag) ?_ ?_ _ hx
  · rfl
  intro a b st hb hf
  peel hf
  all_goals (cases hf; simpa using hb)

theorem stepRead1_tg {s s' : RState} {m : Read1ProxiedM} {o : List Out}
    (h : stepRead1 s m = .ok (s', o)) : TG s s' := by
  unfold stepRead1 at h; tg_close h

theorem stepRead2_tg {s s' : RState} {m : Read2ProxiedM} {o : List Out}
    (h : stepRead2 s m = .ok (s', o)) : TG s s' := by
  unfold stepRead2 at h; tg_close h

theorem stepWrite1_tg {s s' : RState} {m : Write1ProxiedM} {o : List Out}
    (h : stepWrite1 s m = .ok (s', o)) : TG s s' := by
  unfold stepWrite1 at h; tg_close h

theorem stepWrite2_tg {s s' : RState} {m : Write2ProxiedM} {o : List Out}
    (h : stepWrite2 s m = .ok (s', o)) : TG s s' := by
  unfold stepWrite2 at h; tg_close h

/-- A step never lowers the store's tag (every handler changes the store only through
`RState.overwrite`). -/
theorem step_tag_mono {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) : tagLe s.tag.toP s'.tag.toP := by
  show TG s s'
  cases e with
  | read => exact stepClientRead_tg h
  | write => exact stepClientWrite_tg h
  | rmw => exact stepClientRMW_tg h
  | forceWrite => cases h; exact tagLe_refl _
  | recover => exact stepRecover_tg h
  | exec => exact stepExec_tg h
  | msg m =>
    cases m with
    | read1 => exact stepRead1_tg h
    | read2 => exact stepRead2_tg h
    | write1 => exact stepWrite1_tg h
    | write2 => exact stepWrite2_tg h
    | read1Reply => exact stepRead1Reply_tg h
    | read2Reply => exact stepRead2Reply_tg h
    | write1Reply => exact stepWrite1Reply_tg h
    | write2Reply => exact stepWrite2Reply_tg h
    | prepare => exact stepPrepare_tg h
    | preAccept => exact stepPreAccept_tg h
    | accept => exact stepAccept_tg h
    | commit => exact stepCommit_tg h
    | prepareReply => exact stepPrepareReply_tg h
    | preAcceptReply => exact stepPreAcceptReply_tg h
    | preAcceptOK => exact stepPreAcceptOK_tg h
    | acceptReply => exact stepAcceptReply_tg h
    | executed => exact handleExecuted_tg h
    | executeOverwrite => exact stepExecuteOverwrite_tg h

end Perennial.gryff.pure
