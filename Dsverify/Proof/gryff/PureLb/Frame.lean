/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/Frame.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: **the read-record frame** of the steps: every handler but the client requests and the
Gryff register handlers keeps the coordinator's read records, ongoing requests, `maxN`, `nReqs`
(`FR`), and sends no read-path or `Write2`-path message, nor a read reply (`NoR`). One lemma per
handler, by `peel` (as unit L's `PureL/Frame.lean`).
-/
module

public import Dsverify.Proof.gryff.PureL.Frame

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

/-- The messages of the read records' (and the `Write2`s') accounting. -/
def isRMsg : Msg → Bool
  | .read1 _ => true
  | .read1Reply _ => true
  | .read2 _ => true
  | .read2Reply _ => true
  | .write2 _ => true
  | .write2Reply _ => true
  | _ => false

def isROut : Out → Bool
  | .send _ m => isRMsg m
  | .ext (.readReply ..) => true
  | .ext (.writeReply ..) => true
  | .ext _ => false

/-- No read-path message nor read or write reply among outputs. -/
def NoR (o : List Out) : Prop := ∀ x ∈ o, isROut x = false

/-- The fields of the read accounting are kept. -/
def FR (s s' : RState) : Prop :=
  s'.rops = s.rops ∧ s'.ongoingReqs = s.ongoingReqs ∧ s'.maxN = s.maxN ∧ s'.nReqs = s.nReqs

theorem FR.rfl' {s : RState} : FR s s := ⟨rfl, rfl, rfl, rfl⟩
theorem FR.trans' {a b c : RState} (h1 : FR a b) (h2 : FR b c) : FR a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

theorem noR_nil : NoR [] := by simp [NoR]
theorem noR_append {a b : List Out} (ha : NoR a) (hb : NoR b) : NoR (a ++ b) := by
  intro x hx; rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h
theorem noR_single {x : Out} (h : isROut x = false) : NoR [x] := by
  intro y hy; rw [List.mem_singleton.1 hy]; exact h

theorem sendTo_isR {q : w32} {m : Msg} {x : Out} (h : sendTo q m = some x) :
    isROut x = isRMsg m := by
  unfold sendTo at h
  obtain ⟨d, _, rfl⟩ := Option.map_eq_some_iff.1 h; rfl

theorem sendPeer_isR {s : RState} {q : w32} {m : Msg} {x : Out} (h : sendPeer s q m = some x) :
    isROut x = isRMsg m := by
  unfold sendPeer at h; split at h
  · cases h
  · exact sendTo_isR h

theorem mapM_sendTo_isR {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendTo q m) = some r) : ∀ y ∈ r, isROut y = isRMsg m := by
  intro y hy
  obtain ⟨a, _, h'⟩ := mapM_some_mem h y hy
  exact sendTo_isR h'

theorem mapM_sendPeer_isR {s : RState} {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendPeer s q m) = some r) : ∀ y ∈ r, isROut y = isRMsg m := by
  intro y hy
  obtain ⟨a, _, h'⟩ := mapM_some_mem h y hy
  exact sendPeer_isR h'

theorem bcast_noR {s : RState} {m : Msg} {r : List Out} (h : bcast s m = some r)
    (hm : isRMsg m = false) : NoR r := by
  intro y hy; rw [mapM_sendPeer_isR h y hy]; exact hm

theorem bcastPreAccept_noR {s : RState} {a b c : w32} {cs : List Cmd} {sq : w32} {d : Deps}
    {v : ValTag} {r : List Out} (h : bcastPreAccept s a b c cs sq d v = some r) : NoR r :=
  bcast_noR h rfl
theorem bcastAccept_noR {s : RState} {a b c : w32} {cs : List Cmd} {sq : w32} {d : Deps}
    {v : ValTag} {r : List Out} (h : bcastAccept s a b c cs sq d v = some r) : NoR r :=
  bcast_noR h rfl
theorem bcastCommit_noR {s : RState} {a b : w32} {cs : List Cmd} {sq : w32} {d : Deps}
    {v : ValTag} {r : List Out} (h : bcastCommit s a b cs sq d v = some r) : NoR r :=
  bcast_noR h rfl
theorem bcastPrepare_noR {s : RState} {a b c : w32} {r : List Out}
    (h : bcastPrepare s a b c = some r) : NoR r :=
  bcast_noR h rfl

theorem updateConflicts_fr (s : RState) (cmds : List Cmd) (q i sq : w32) :
    FR s (updateConflicts s cmds q i sq) := by
  unfold updateConflicts
  apply forIn_id_inv (P := fun x : RState => FR s x) _ _ _ FR.rfl'
  intro a b hb
  simpa [FR] using hb

theorem updateCommitted_fr {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    FR s s' := by
  unfold updateCommitted at h; opeel h
  all_goals (cases h; exact FR.rfl')

theorem overwrite_fr (s : RState) (v : w64) (t : model.Tag) : FR s (s.overwrite v t) := by
  unfold RState.overwrite; split <;> exact FR.rfl'

theorem updateConflicts_rops (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).rops = s.rops := (updateConflicts_fr s cmds q i sq).1
theorem updateConflicts_ongoingReqs (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).ongoingReqs = s.ongoingReqs :=
  (updateConflicts_fr s cmds q i sq).2.1
theorem updateConflicts_maxN (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).maxN = s.maxN := (updateConflicts_fr s cmds q i sq).2.2.1
theorem updateConflicts_nReqs (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).nReqs = s.nReqs := (updateConflicts_fr s cmds q i sq).2.2.2
theorem overwrite_rops (s : RState) (v : w64) (t : model.Tag) : (s.overwrite v t).rops = s.rops :=
  (overwrite_fr s v t).1
theorem overwrite_ongoingReqs (s : RState) (v : w64) (t : model.Tag) :
    (s.overwrite v t).ongoingReqs = s.ongoingReqs := (overwrite_fr s v t).2.1
theorem overwrite_maxN (s : RState) (v : w64) (t : model.Tag) : (s.overwrite v t).maxN = s.maxN :=
  (overwrite_fr s v t).2.2.1
theorem overwrite_nReqs (s : RState) (v : w64) (t : model.Tag) :
    (s.overwrite v t).nReqs = s.nReqs := (overwrite_fr s v t).2.2.2

macro "fr_fin_st" : tactic => `(tactic| (
  unfold FR
  try (have hu := updateCommitted_fr ‹updateCommitted _ _ = some _›; unfold FR at hu
       simp only [hu.1, hu.2.1, hu.2.2.1, hu.2.2.2])
  try simp only [RState.setInst, RState.setCrt, updateConflicts_rops, updateConflicts_ongoingReqs,
    updateConflicts_maxN, updateConflicts_nReqs, overwrite_rops, overwrite_ongoingReqs,
    overwrite_maxN, overwrite_nReqs]
  try (have hu := updateCommitted_fr ‹updateCommitted _ _ = some _›; unfold FR at hu
       simp only [hu.1, hu.2.1, hu.2.2.1, hu.2.2.2])
  try simp only [RState.setInst, RState.setCrt, updateConflicts_rops, updateConflicts_ongoingReqs,
    updateConflicts_maxN, updateConflicts_nReqs, overwrite_rops, overwrite_ongoingReqs,
    overwrite_maxN, overwrite_nReqs]
  try exact ⟨rfl, rfl, rfl, rfl⟩
  try exact ⟨trivial, trivial, trivial, trivial⟩))

macro "fr_fin" : tactic => `(tactic| (
  refine ⟨?_, ?_⟩
  · fr_fin_st
  · first
    | exact noR_nil
    | exact noR_single rfl
    | with_reducible exact bcastPreAccept_noR ‹_›
    | with_reducible exact bcastAccept_noR ‹_›
    | with_reducible exact bcastCommit_noR ‹_›
    | with_reducible exact bcastPrepare_noR ‹_›
    | with_reducible exact noR_single ((sendPeer_isR ‹sendPeer _ _ _ = some _›).trans rfl)
    | with_reducible exact noR_single ((sendTo_isR ‹sendTo _ _ = some _›).trans rfl)
    | (intro y hy; with_reducible exact (mapM_sendTo_isR ‹_› y hy).trans rfl)
    | (intro y hy; with_reducible exact (mapM_sendPeer_isR ‹_› y hy).trans rfl)))

theorem startPhase1_fr {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o)) : FR s s' ∧ NoR o := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; fr_fin)

theorem leaderCommit_fr {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit s q i c lb = .ok (s', o)) : FR s s' ∧ NoR o := by
  unfold leaderCommit at h; peel h
  all_goals (cases h; fr_fin)

macro "fr_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; fr_fin; done)
    | (have hh := leaderCommit_fr $h:ident
       exact ⟨FR.trans' (by fr_fin_st) hh.1, hh.2⟩)
    | (have hh := startPhase1_fr $h:ident
       exact ⟨FR.trans' (by fr_fin_st) hh.1, hh.2⟩))))

theorem handleExecuted_fr {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) : FR s s' ∧ NoR o := by
  unfold handleExecuted at h; fr_close h

theorem stepPreAccept_fr {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) : FR s s' ∧ NoR o := by
  unfold stepPreAccept at h; fr_close h

theorem stepPreAcceptReply_fr {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) : FR s s' ∧ NoR o := by
  unfold stepPreAcceptReply at h; fr_close h

theorem stepPreAcceptOK_fr {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) : FR s s' ∧ NoR o := by
  unfold stepPreAcceptOK at h; fr_close h

theorem stepAccept_fr {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) : FR s s' ∧ NoR o := by
  unfold stepAccept at h; fr_close h

theorem stepAcceptReply_fr {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) : FR s s' ∧ NoR o := by
  unfold stepAcceptReply at h; fr_close h

theorem stepCommit_fr {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) : FR s s' ∧ NoR o := by
  unfold stepCommit at h; fr_close h

theorem stepPrepare_fr {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) : FR s s' ∧ NoR o := by
  unfold stepPrepare at h; fr_close h

theorem stepPrepareReply_fr {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) : FR s s' ∧ NoR o := by
  unfold stepPrepareReply at h; fr_close h

theorem stepRecover_fr {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) : FR s s' ∧ NoR o := by
  unfold stepRecover at h; fr_close h

theorem stepExec_fr {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) : FR s s' ∧ NoR o := by
  unfold stepExec at h; fr_close h

theorem stepExecuteOverwrite_fr {s s' : RState} {m : ExecuteOverwriteM} {o : List Out}
    (h : stepExecuteOverwrite s m = .ok (s', o)) : FR s s' ∧ NoR o := by
  unfold stepExecuteOverwrite at h
  peel h
  all_goals (first
    | (cases h; fr_fin; done)
    | (have hh := handleExecuted_fr h
       exact ⟨FR.trans' (by fr_fin_st) hh.1, hh.2⟩))

/-- The events with their own read-accounting lemma. -/
def Ev.rspecial : Ev → Bool
  | .read .. => true
  | .write .. => true
  | .rmw .. => true
  | .msg (.read1 _) => true
  | .msg (.read2 _) => true
  | .msg (.write1 _) => true
  | .msg (.write2 _) => true
  | .msg (.read1Reply _) => true
  | .msg (.read2Reply _) => true
  | .msg (.write1Reply _) => true
  | .msg (.write2Reply _) => true
  | _ => false

/-- Every other step keeps the read accounting. -/
theorem step_fr_other {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) (he : Ev.rspecial e = false) : FR s s' ∧ NoR o := by
  cases e with
  | read => cases he
  | write => cases he
  | rmw => cases he
  | forceWrite => cases h; exact ⟨FR.rfl', noR_nil⟩
  | recover => exact stepRecover_fr h
  | exec => exact stepExec_fr h
  | msg m =>
    cases m with
    | prepare => exact stepPrepare_fr h
    | preAccept => exact stepPreAccept_fr h
    | accept => exact stepAccept_fr h
    | commit => exact stepCommit_fr h
    | prepareReply => exact stepPrepareReply_fr h
    | preAcceptReply => exact stepPreAcceptReply_fr h
    | preAcceptOK => exact stepPreAcceptOK_fr h
    | acceptReply => exact stepAcceptReply_fr h
    | executed => exact handleExecuted_fr h
    | executeOverwrite => exact stepExecuteOverwrite_fr h
    | _ => cases he

end Perennial.gryff.pure
