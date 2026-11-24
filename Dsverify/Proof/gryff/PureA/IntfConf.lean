/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/IntfConf.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AI, internal: every handler only raises the conflict table (`ConfLe s s'`; only
`updateConflicts` writes it), per handler by unit L's `peel` (same pattern as A1's `*_keep`).
-/
module

public import Dsverify.Proof.gryff.PureA.IntfSteps

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AI

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA

theorem confLe_uc {s t : RState} (h : ConfLe s t) (cmds : List Cmd) (q i sq : w32) :
    ConfLe s (updateConflicts t cmds q i sq) := h.trans (uc_facts t cmds q i sq).1

theorem updateCommitted_conf {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    s'.conf = s.conf := by
  unfold updateCommitted at h; opeel h
  all_goals (cases h; rfl)

theorem overwrite_conf (s : RState) (v : w64) (t : model.Tag) : (s.overwrite v t).conf = s.conf := by
  unfold RState.overwrite; split <;> rfl

macro "conf_fin" : tactic => `(tactic| (
  first
    | exact confLe_of_eq rfl
    | exact (confLe_of_eq rfl).trans (uc_facts _ _ _ _ _).1
    | (obtain hU := ‹updateCommitted _ _ = some _›
       refine ConfLe.trans ?_ (confLe_of_eq (updateCommitted_conf hU))
       first
         | exact confLe_of_eq rfl
         | exact (confLe_of_eq rfl).trans (uc_facts _ _ _ _ _).1)))

set_option maxRecDepth 20000

theorem leaderCommit_conf {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit s q i c lb = .ok (s', o)) : ConfLe s s' := by
  unfold leaderCommit at h; peel h
  all_goals (cases h; obtain hU := ‹updateCommitted _ _ = some _›; apply confLe_of_eq
             have := updateCommitted_conf hU; exact this)

theorem startPhase1_conf {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o)) : ConfLe s s' := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; conf_fin)

macro "conf_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; conf_fin; done)
    | exact leaderCommit_conf $h:ident
    | exact startPhase1_conf $h:ident
    | (cases $h:ident; exact confLe_of_eq rfl))))


theorem stepPreAccept_conf {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) : ConfLe s s' := by
  unfold stepPreAccept at h; conf_close h
theorem stepAccept_conf {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) : ConfLe s s' := by
  unfold stepAccept at h; conf_close h
theorem stepCommit_conf {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) : ConfLe s s' := by
  unfold stepCommit at h; conf_close h
theorem stepPreAcceptReply_conf {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) : ConfLe s s' := by
  unfold stepPreAcceptReply at h; conf_close h
theorem stepPreAcceptOK_conf {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) : ConfLe s s' := by
  unfold stepPreAcceptOK at h; conf_close h
theorem stepAcceptReply_conf {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) : ConfLe s s' := by
  unfold stepAcceptReply at h; conf_close h
theorem stepPrepare_conf {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) : ConfLe s s' := by
  unfold stepPrepare at h; conf_close h
theorem stepRecover_conf {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) : ConfLe s s' := by
  unfold stepRecover at h; conf_close h

end Perennial.gryff.pureA.AI
