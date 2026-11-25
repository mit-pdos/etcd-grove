/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLc/FrameC.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-c: the executor's chain frame: every handler but the executor keeps `PrevValTag`; the
instance counters `crtInstance` only grow (signed), and an RMW request raises its own row's by one.
Same technique as `PureL/Frame.lean` (`peel`, a closing macro per handler).
-/
module

public import Dsverify.Proof.gryff.PureL.StoreSteps
public import Dsverify.Proof.gryff.PureL.Frame
public import Dsverify.Proof.gryff.PureL.WRec

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

/-- The chain frame: `PrevValTag`, the id and the instance counters kept. -/
def PF (s s' : RState) : Prop :=
  s'.prevValTag = s.prevValTag ∧ s'.id = s.id ∧ s'.crtInstance = s.crtInstance

theorem PF.rfl' {s : RState} : PF s s := ⟨rfl, rfl, rfl⟩
theorem PF.trans' {a b c : RState} (h1 : PF a b) (h2 : PF b c) : PF a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem updateConflicts_pf (s : RState) (cmds : List Cmd) (q i sq : w32) :
    PF s (updateConflicts s cmds q i sq) := by
  unfold updateConflicts
  apply forIn_id_inv (P := fun x : RState => PF s x) _ _ _ PF.rfl'
  intro a b hb
  simpa [PF] using hb

theorem updateCommitted_pf {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    PF s s' := by
  unfold updateCommitted at h; opeel h
  all_goals (cases h; exact PF.rfl')

theorem overwrite_pf (s : RState) (v : w64) (t : model.Tag) : PF s (s.overwrite v t) := by
  unfold RState.overwrite; split <;> exact PF.rfl'

theorem updateConflicts_prev (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).prevValTag = s.prevValTag := (updateConflicts_pf s cmds q i sq).1
theorem updateConflicts_crt (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).crtInstance = s.crtInstance :=
  (updateConflicts_pf s cmds q i sq).2.2
theorem overwrite_prev (s : RState) (v : w64) (t : model.Tag) :
    (s.overwrite v t).prevValTag = s.prevValTag := (overwrite_pf s v t).1
theorem overwrite_crt (s : RState) (v : w64) (t : model.Tag) :
    (s.overwrite v t).crtInstance = s.crtInstance := (overwrite_pf s v t).2.2

macro "pf_fin" : tactic => `(tactic| (
  unfold PF
  try (have hu := updateCommitted_pf ‹updateCommitted _ _ = some _›; unfold PF at hu
       simp only [hu.1, hu.2.1, hu.2.2])
  try simp only [RState.setInst, RState.setCrt, updateConflicts_prev, updateConflicts_id,
    updateConflicts_crt, overwrite_prev, overwrite_id, overwrite_crt]
  try (have hu := updateCommitted_pf ‹updateCommitted _ _ = some _›; unfold PF at hu
       simp only [hu.1, hu.2.1, hu.2.2])
  try simp only [RState.setInst, RState.setCrt, updateConflicts_prev, updateConflicts_id,
    updateConflicts_crt, overwrite_prev, overwrite_id, overwrite_crt]
  try exact ⟨rfl, rfl, rfl⟩
  try exact ⟨trivial, trivial, trivial⟩))

theorem startPhase1_pf {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o)) : PF s s' := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; pf_fin)

theorem leaderCommit_pf {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit s q i c lb = .ok (s', o)) : PF s s' := by
  unfold leaderCommit at h; peel h
  all_goals (cases h; pf_fin)

macro "pf_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; pf_fin; done)
    | (exact PF.trans' (by pf_fin) (leaderCommit_pf $h:ident))
    | (exact PF.trans' (by pf_fin) (startPhase1_pf $h:ident)))))

theorem handleExecuted_pf {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) : PF s s' := by
  unfold handleExecuted at h; pf_close h

theorem shortCircuit_pf {s s' : RState} {n : w32} {v : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n v f = some (s', o)) : PF s s' := by
  rcases Perennial.gryff.model.shortCircuit_cases h with h | ⟨rfl, rfl⟩
  rotate_left
  · exact PF.rfl'
  unfold Perennial.gryff.model.shortCircuitReads at h
  opeel h
  all_goals
    cases h
    refine forIn_opt_inv _ _ _ (fun p : RState × List Out => PF s p.1) PF.rfl' ?_ _ ‹_›
    intro a b st hb hf
    opeel hf
    all_goals (cases hf; exact hb)

theorem shortCircuit_ite_pf {s s' : RState} {c : Prop} [Decidable c] {n : w32} {v : ValTag}
    {f : Bool} {o : List Out}
    (h : (if c then shortCircuit s n v f else some (s, [])) = some (s', o)) : PF s s' := by
  split at h
  · exact shortCircuit_pf h
  · cases h; exact PF.rfl'

theorem stepRead1Reply_pf {s s' : RState} {m : Read1ReplyM} {o : List Out}
    (h : stepRead1Reply s m = .ok (s', o)) : PF s s' := by
  unfold stepRead1Reply at h; pf_close h

theorem stepRead2Reply_pf {s s' : RState} {m : Read2ReplyM} {o : List Out}
    (h : stepRead2Reply s m = .ok (s', o)) : PF s s' := by
  unfold stepRead2Reply at h; pf_close h

theorem stepPreAcceptReply_pf {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) : PF s s' := by
  unfold stepPreAcceptReply at h; pf_close h

theorem stepPreAcceptOK_pf {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) : PF s s' := by
  unfold stepPreAcceptOK at h; pf_close h

theorem stepAcceptReply_pf {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) : PF s s' := by
  unfold stepAcceptReply at h; pf_close h

theorem stepPrepare_pf {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) : PF s s' := by
  unfold stepPrepare at h; pf_close h

theorem stepPrepareReply_pf {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) : PF s s' := by
  unfold stepPrepareReply at h; pf_close h

theorem stepRecover_pf {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) : PF s s' := by
  unfold stepRecover at h; pf_close h

theorem stepRead1_pf {s s' : RState} {m : Read1ProxiedM} {o : List Out}
    (h : stepRead1 s m = .ok (s', o)) : PF s s' := by
  unfold stepRead1 at h; pf_close h

theorem stepRead2_pf {s s' : RState} {m : Read2ProxiedM} {o : List Out}
    (h : stepRead2 s m = .ok (s', o)) : PF s s' := by
  unfold stepRead2 at h; pf_close h

theorem stepWrite2_pf {s s' : RState} {m : Write2ProxiedM} {o : List Out}
    (h : stepWrite2 s m = .ok (s', o)) : PF s s' := by
  unfold stepWrite2 at h; pf_close h

theorem stepWrite1_pf {s s' : RState} {m : Write1ProxiedM} {o : List Out}
    (h : stepWrite1 s m = .ok (s', o)) : PF s s' := by
  unfold stepWrite1 at h; pf_close h

theorem stepExecuteOverwrite_pf {s s' : RState} {m : ExecuteOverwriteM} {o : List Out}
    (h : stepExecuteOverwrite s m = .ok (s', o)) : PF s s' := by
  unfold stepExecuteOverwrite at h
  peel h
  all_goals (first
    | (cases h; pf_fin; done)
    | (exact PF.trans' (by pf_fin) (handleExecuted_pf h)))

theorem stepWrite1Reply_pf {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) : PF s s' := by
  unfold stepWrite1Reply at h
  peel h
  all_goals (cases h)
  all_goals (try (have hsc := shortCircuit_pf ‹shortCircuit _ _ _ _ = some _›))
  all_goals (first | (pf_fin; done) | (exact PF.trans' (by pf_fin) hsc) | skip)

theorem stepWrite2Reply_pf {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (h : stepWrite2Reply s m = .ok (s', o)) : PF s s' := by
  unfold stepWrite2Reply at h
  peel h
  all_goals (cases h)
  all_goals (try (have hsc := shortCircuit_ite_pf ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›))
  all_goals (first | (pf_fin; done) | (exact PF.trans' (by pf_fin) hsc) | skip)

theorem stepClientRead_pf {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {o : List Out}
    (h : stepClientRead s rid cid k d = .ok (s', o)) : PF s s' := by
  unfold stepClientRead at h
  peel h
  cases h
  have hx := ‹forIn _ _ _ = Except.ok s'›
  refine forIn_exc_inv _ _ _ (fun x : RState => PF s x) ?_ ?_ _ hx
  · exact PF.rfl'
  intro a b st hb hf
  peel hf
  all_goals (cases hf; exact hb)

theorem stepClientWrite_pf {s s' : RState} {rid cid : w32} {k v : w64} {d : Dep} {o : List Out}
    (h : stepClientWrite s rid cid k v d = .ok (s', o)) : PF s s' := by
  unfold stepClientWrite at h
  peel h
  cases h; pf_fin

/-- A step that may raise one instance counter (`if sge inst crt[q] then crt[q] := inst + 1`). -/
def PFs (s s' : RState) : Prop :=
  PF s s' ∨ ∃ q x, inBox q x = true ∧ sge x (s.crt q) = true ∧ PF (s.setCrt q (x + 1)) s'

macro "pfs_fin" : tactic => `(tactic| (first
  | (left; pf_fin; done)
  | (right; refine ⟨_, _, by simpa using ‹¬(!inBox _ _) = true›, ‹sge _ _ = true›, ?_⟩; pf_fin; done)))

theorem stepAccept_pfs {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) : PFs s s' := by
  unfold stepAccept at h
  peel h
  all_goals (cases h; pfs_fin)

theorem stepCommit_pfs {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) : PFs s s' := by
  unfold stepCommit at h
  peel h
  all_goals (cases h; pfs_fin)

theorem stepPreAccept_pfs {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) : PFs s s' := by
  unfold stepPreAccept at h
  peel h
  all_goals (cases h; pfs_fin)

theorem startPhase1_inBox {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o)) : inBox q i = true := by
  unfold startPhase1 at h; peel h
  all_goals (simpa using ‹¬(!inBox _ _) = true›)

theorem stepClientRMW_pc {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    {o : List Out} (h : stepClientRMW s rid cid k d a b = .ok (s', o)) :
    PF (s.setCrt s.id (s.crt s.id + 1)) s' ∧ inBox s.id (s.crt s.id) = true := by
  unfold stepClientRMW at h
  peel h
  obtain ⟨-, -, h⟩ := handlePropose_ok h; unfold handleProposeBody at h
  refine ⟨PF.trans' (by unfold PF; simp [RState.setCrt, RState.crt])
    (startPhase1_pf h), ?_⟩
  have := startPhase1_inBox h
  simpa [RState.setCrt, RState.crt] using this

theorem stepExec_pc {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) : s'.id = s.id ∧ s'.crtInstance = s.crtInstance ∧
      ((execRes o = none ∧ s'.prevValTag = s.prevValTag) ∨
        ∃ vt, execRes o = some vt ∧ s'.prevValTag = some vt) := by
  unfold stepExec at h
  peel h
  all_goals (cases h)
  · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  all_goals
    obtain ⟨d, rfl⟩ := sendTo_some ‹sendTo _ _ = some _›
    refine ⟨rfl, rfl, Or.inr ⟨_, rfl, ?_⟩⟩
    simp only [RState.setInst]
    (repeat' split) <;> simp_all

/-- Raising an instance counter under the handlers' guard raises it (signed, no wrap). -/
theorem crt_setCrt_le {s : RState} {q x : w32} (hb : inBox q x = true) (hs : sge x (s.crt q) = true)
    (q' : w32) : sint.Z (s.crt q') ≤ sint.Z ((s.setCrt q (x + 1)).crt q') := by
  have hb' : sint.Z x < 2 * 1024 * 1024 := by
    unfold inBox at hb; have := of_decide_eq_true hb; unfold SLOTS at this; omega
  simp only [sge, sle, decide_eq_true_eq] at hs
  have hx : sint.Z (x + 1) = sint.Z x + 1 := Z_succ32 (by omega)
  unfold RState.crt RState.setCrt at *
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set] at *
  by_cases hq : q.toNat = q'.toNat
  · rw [if_pos hq]; rw [hq] at hs
    split
    · simp only [Option.getD_some]; omega
    · rename_i hlen
      rw [List.getElem?_eq_none (by omega)]; exact Int.le_refl _
  · rw [if_neg hq]; exact Int.le_refl _

theorem PFs.crt_le {s s' : RState} (h : PFs s s') (q : w32) : sint.Z (s.crt q) ≤ sint.Z (s'.crt q) := by
  rcases h with h | ⟨q0, x, hb, hs, h⟩
  · unfold RState.crt; rw [h.2.2]; exact Int.le_refl _
  · have := crt_setCrt_le hb hs q
    unfold RState.crt at *; rw [h.2.2]; exact this

theorem PF.pfs {s s' : RState} (h : PF s s') : PFs s s' := Or.inl h

/-- The chain frame over every step: the id is kept, the instance counters only grow, and only
an execution changes `PrevValTag` (`stepExec_pc`). -/
theorem step_pc {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) :
    s'.id = s.id ∧ (∀ q, sint.Z (s.crt q) ≤ sint.Z (s'.crt q)) ∧
      ((∀ q i, e ≠ .exec q i) → s'.prevValTag = s.prevValTag) := by
  have of_pfs : PFs s s' → s'.id = s.id ∧ (∀ q, sint.Z (s.crt q) ≤ sint.Z (s'.crt q)) ∧
      ((∀ q i, e ≠ .exec q i) → s'.prevValTag = s.prevValTag) := by
    intro hp
    refine ⟨?_, hp.crt_le, fun _ => ?_⟩
    · rcases hp with hp | ⟨_, _, _, _, hp⟩
      · exact hp.2.1
      · exact hp.2.1
    · rcases hp with hp | ⟨_, _, _, _, hp⟩
      · exact hp.1
      · exact hp.1
  cases e with
  | read => exact of_pfs (stepClientRead_pf h).pfs
  | write => exact of_pfs (stepClientWrite_pf h).pfs
  | rmw =>
    have hh := stepClientRMW_pc h
    refine ⟨hh.1.2.1, fun q => ?_, fun _ => hh.1.1⟩
    have hb := hh.2
    have := crt_setCrt_le (s := s) hb (by simp [sge, sle]) q
    unfold RState.crt at *; rw [hh.1.2.2]; exact this
  | forceWrite => cases h; exact ⟨rfl, fun _ => Int.le_refl _, fun _ => rfl⟩
  | recover => exact of_pfs (stepRecover_pf h).pfs
  | exec q i =>
    have hh := stepExec_pc h
    refine ⟨hh.1, fun q' => ?_, fun hne => absurd rfl (hne q i)⟩
    unfold RState.crt; rw [hh.2.1]; exact Int.le_refl _
  | msg m =>
    cases m with
    | read1 => exact of_pfs (stepRead1_pf h).pfs
    | read2 => exact of_pfs (stepRead2_pf h).pfs
    | write1 => exact of_pfs (stepWrite1_pf h).pfs
    | write2 => exact of_pfs (stepWrite2_pf h).pfs
    | read1Reply => exact of_pfs (stepRead1Reply_pf h).pfs
    | read2Reply => exact of_pfs (stepRead2Reply_pf h).pfs
    | write1Reply => exact of_pfs (stepWrite1Reply_pf h).pfs
    | write2Reply => exact of_pfs (stepWrite2Reply_pf h).pfs
    | prepare => exact of_pfs (stepPrepare_pf h).pfs
    | preAccept => exact of_pfs (stepPreAccept_pfs h)
    | accept => exact of_pfs (stepAccept_pfs h)
    | commit => exact of_pfs (stepCommit_pfs h)
    | prepareReply => exact of_pfs (stepPrepareReply_pf h).pfs
    | preAcceptReply => exact of_pfs (stepPreAcceptReply_pf h).pfs
    | preAcceptOK => exact of_pfs (stepPreAcceptOK_pf h).pfs
    | acceptReply => exact of_pfs (stepAcceptReply_pf h).pfs
    | executed => exact of_pfs (handleExecuted_pf h).pfs
    | executeOverwrite => exact of_pfs (stepExecuteOverwrite_pf h).pfs

theorem PFs.len {s s' : RState} (h : PFs s s') : s'.crtInstance.length = s.crtInstance.length := by
  rcases h with h | ⟨q0, x, hb, hs, h⟩
  · rw [h.2.2]
  · rw [h.2.2]; simp [RState.setCrt]

/-- Every step keeps the length of the instance counters. -/
theorem step_crt_len {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) : s'.crtInstance.length = s.crtInstance.length := by
  cases e with
  | read => exact (stepClientRead_pf h).pfs.len
  | write => exact (stepClientWrite_pf h).pfs.len
  | rmw => rw [(stepClientRMW_pc h).1.2.2]; simp [RState.setCrt]
  | forceWrite => cases h; rfl
  | recover => exact (stepRecover_pf h).pfs.len
  | exec q i => rw [(stepExec_pc h).2.1]
  | msg m =>
    cases m with
    | read1 => exact (stepRead1_pf h).pfs.len
    | read2 => exact (stepRead2_pf h).pfs.len
    | write1 => exact (stepWrite1_pf h).pfs.len
    | write2 => exact (stepWrite2_pf h).pfs.len
    | read1Reply => exact (stepRead1Reply_pf h).pfs.len
    | read2Reply => exact (stepRead2Reply_pf h).pfs.len
    | write1Reply => exact (stepWrite1Reply_pf h).pfs.len
    | write2Reply => exact (stepWrite2Reply_pf h).pfs.len
    | prepare => exact (stepPrepare_pf h).pfs.len
    | preAccept => exact (stepPreAccept_pfs h).len
    | accept => exact (stepAccept_pfs h).len
    | commit => exact (stepCommit_pfs h).len
    | prepareReply => exact (stepPrepareReply_pf h).pfs.len
    | preAcceptReply => exact (stepPreAcceptReply_pf h).pfs.len
    | preAcceptOK => exact (stepPreAcceptOK_pf h).pfs.len
    | acceptReply => exact (stepAcceptReply_pf h).pfs.len
    | executed => exact (handleExecuted_pf h).pfs.len
    | executeOverwrite => exact (stepExecuteOverwrite_pf h).pfs.len

/-- An RMW request raises its replica's own instance counter by one. -/
theorem stepRMW_crt {r : Fin 3} {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    {o : List Out} (h : stepR r s (.rmw rid cid k d a b) = .ok (s', o))
    (hlen : (s.id).toNat < s.crtInstance.length) :
    sint.Z (s'.crt s.id) = sint.Z (s.crt s.id) + 1 := by
  have hh := stepClientRMW_pc h
  have hb := hh.2
  have hb' : sint.Z (s.crt s.id) < 2 * 1024 * 1024 := by
    unfold inBox at hb; have := of_decide_eq_true hb; unfold SLOTS at this; omega
  have hz := Z_succ32 (x := s.crt s.id) (by omega)
  rw [← hz]
  unfold RState.crt; rw [hh.1.2.2]
  simp only [RState.setCrt, List.getD_eq_getElem?_getD, List.getElem?_set_self hlen,
    Option.getD_some]
  rfl

end Perennial.gryff.pure
