/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLa/NReqs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-a: only the client requests count in `RState.nReqs` (a lemma per handler, by peeling).
-/
module

public import Dsverify.Proof.gryff.PureLa.Defs

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.La

open model kahn Perennial.gryff.pure

theorem nReqs_updateConflicts (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).nReqs = s.nReqs := (updateConflicts_fields s cmds q i sq).2.2.2.2.2

theorem nReqs_overwrite (s : RState) (v : w64) (t : model.Tag) : (s.overwrite v t).nReqs = s.nReqs := by
  unfold RState.overwrite; split <;> rfl

theorem nReqs_shortCircuit {s s' : RState} {n : w32} {v : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n v f = some (s', o)) : s'.nReqs = s.nReqs := by
  unfold shortCircuit at h
  opeel h
  all_goals
    cases h
    refine forIn_opt_inv _ _ _ (fun p : RState × List Out => p.1.nReqs = s.nReqs) rfl ?_ _ ‹_›
    intro a b st hb hf
    opeel hf
    all_goals (cases hf; exact hb)

theorem nReqs_shortCircuit_ite {s s' : RState} {c : Prop} [Decidable c] {n : w32} {v : ValTag}
    {f : Bool} {o : List Out}
    (h : (if c then shortCircuit s n v f else some (s, [])) = some (s', o)) : s'.nReqs = s.nReqs := by
  split at h
  · exact nReqs_shortCircuit h
  · cases h; rfl

macro "nr_fin" : tactic => `(tactic| (
  try (have hu := ‹updateCommitted _ _ = some _›; rw [(updateCommitted_fields hu).2.2.2.2.2])
  try (have hu := ‹shortCircuit _ _ _ _ = some _›; rw [nReqs_shortCircuit hu])
  try (have hu := ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›; rw [nReqs_shortCircuit_ite hu])
  try simp only [nReqs_updateConflicts, nReqs_overwrite, RState.setInst, RState.setCrt]
  try (have hu := ‹updateCommitted _ _ = some _›; rw [(updateCommitted_fields hu).2.2.2.2.2])
  try simp only [nReqs_updateConflicts, nReqs_overwrite, RState.setInst, RState.setCrt]))

theorem startPhase1_nr {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; nr_fin)

theorem handleExecuted_nr {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold handleExecuted at h; peel h
  all_goals (cases h; nr_fin)

theorem leaderCommit_nr {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit s q i c lb = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold leaderCommit at h; peel h
  all_goals (cases h; nr_fin)

macro "nr_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; nr_fin; done)
    | (rw [leaderCommit_nr $h:ident]; nr_fin; done)
    | (rw [startPhase1_nr $h:ident]; nr_fin; done)
    | (rw [handleExecuted_nr $h:ident]; nr_fin; done))))

theorem stepRecover_nr {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepRecover at h; nr_close h

theorem stepExec_nr {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepExec at h; nr_close h

theorem stepRead1_nr {s s' : RState} {m : Read1ProxiedM} {o : List Out}
    (h : stepRead1 s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepRead1 at h; nr_close h

theorem stepRead2_nr {s s' : RState} {m : Read2ProxiedM} {o : List Out}
    (h : stepRead2 s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepRead2 at h; nr_close h

theorem stepRead1Reply_nr {s s' : RState} {m : Read1ReplyM} {o : List Out}
    (h : stepRead1Reply s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepRead1Reply at h; nr_close h

theorem stepRead2Reply_nr {s s' : RState} {m : Read2ReplyM} {o : List Out}
    (h : stepRead2Reply s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepRead2Reply at h; nr_close h

theorem stepWrite1_nr {s s' : RState} {m : Write1ProxiedM} {o : List Out}
    (h : stepWrite1 s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepWrite1 at h; nr_close h

theorem stepWrite2_nr {s s' : RState} {m : Write2ProxiedM} {o : List Out}
    (h : stepWrite2 s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepWrite2 at h; nr_close h

theorem stepWrite1Reply_nr {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepWrite1Reply at h; nr_close h

theorem stepWrite2Reply_nr {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (h : stepWrite2Reply s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepWrite2Reply at h; nr_close h

theorem stepPreAccept_nr {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepPreAccept at h; nr_close h

theorem stepPreAcceptReply_nr {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepPreAcceptReply at h; nr_close h

theorem stepPreAcceptOK_nr {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepPreAcceptOK at h; nr_close h

theorem stepAccept_nr {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepAccept at h; nr_close h

theorem stepAcceptReply_nr {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepAcceptReply at h; nr_close h

theorem stepCommit_nr {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepCommit at h; nr_close h

theorem stepPrepare_nr {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepPrepare at h; nr_close h

theorem stepPrepareReply_nr {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepPrepareReply at h; nr_close h

theorem stepExecuteOverwrite_nr {s s' : RState} {m : ExecuteOverwriteM} {o : List Out}
    (h : stepExecuteOverwrite s m = .ok (s', o)) : s'.nReqs = s.nReqs := by
  unfold stepExecuteOverwrite at h; nr_close h

/-- Client requests (read, write, RMW). -/
def isReqEv : Ev → Bool
  | .read .. => true
  | .write .. => true
  | .rmw .. => true
  | _ => false

theorem step_nReqs {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) (he : isReqEv e = false) : s'.nReqs = s.nReqs := by
  cases e with
  | read => cases he
  | write => cases he
  | rmw => cases he
  | forceWrite => cases h; rfl
  | recover => exact stepRecover_nr h
  | exec => exact stepExec_nr h
  | msg m =>
    cases m with
    | read1 => exact stepRead1_nr h
    | read2 => exact stepRead2_nr h
    | write1 => exact stepWrite1_nr h
    | write2 => exact stepWrite2_nr h
    | read1Reply => exact stepRead1Reply_nr h
    | read2Reply => exact stepRead2Reply_nr h
    | write1Reply => exact stepWrite1Reply_nr h
    | write2Reply => exact stepWrite2Reply_nr h
    | prepare => exact stepPrepare_nr h
    | preAccept => exact stepPreAccept_nr h
    | accept => exact stepAccept_nr h
    | commit => exact stepCommit_nr h
    | prepareReply => exact stepPrepareReply_nr h
    | preAcceptReply => exact stepPreAcceptReply_nr h
    | preAcceptOK => exact stepPreAcceptOK_nr h
    | acceptReply => exact stepAcceptReply_nr h
    | executed => exact handleExecuted_nr h
    | executeOverwrite => exact stepExecuteOverwrite_nr h

end Perennial.gryff.pure.La
