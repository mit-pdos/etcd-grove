/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLc/Cmds.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-c: **the commands invariant** (`exec_cmd`): every carrier of an instance's commands (copies,
their recovery candidates, PreAccept, Accept, Commit, PrepareReply) holds `[]` or a batch whose
first command is the one of the RMW request that created the instance.

The per-handler lemmas are generic in the predicate `P q i cmds` ("a batch of instance `(q, i)`
may be `cmds`"), with `P q i []`; the source is `handlePropose` (`stepClientRMW`).
-/
module

public import Dsverify.Proof.gryff.PureLc.WTag

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

section
variable (P : w32 → w32 → List Cmd → Prop)

/-- A copy of instance `(q, i)` and its recovery candidate carry allowed commands. -/
def CCopyOk (q i : w32) (cp : Copy) : Prop :=
  P q i cp.cmds ∧ ∀ lb ir, cp.lb = some lb → lb.recoveryInst = some ir → P q i ir.cmds

def CSOk (s : RState) : Prop := ∀ q i cp, s.inst q i = some cp → CCopyOk P q i cp

def CMOk : Msg → Prop
  | .preAccept m => P m.replica m.inst m.cmds
  | .accept m => P m.replica m.inst m.cmds
  | .commit m => P m.replica m.inst m.cmds
  | .prepareReply m => P m.replica m.inst m.cmds
  | _ => True

def COOk (o : List Out) : Prop := ∀ x ∈ o, match x with
  | .send _ m => CMOk P m
  | .ext _ => True

end

theorem updateConflicts_inst (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).inst = s.inst := by
  unfold updateConflicts
  apply forIn_id_inv (P := fun x : RState => x.inst = s.inst) _ _ _ rfl
  intro a b hb
  simpa using hb

theorem updateCommitted_inst {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    s'.inst = s.inst := by
  unfold updateCommitted at h; opeel h
  all_goals (cases h; rfl)

theorem overwrite_inst (s : RState) (v : w64) (t : model.Tag) : (s.overwrite v t).inst = s.inst := by
  unfold RState.overwrite; split <;> rfl

section
variable {P : w32 → w32 → List Cmd → Prop}

theorem CSOk.setInst {s : RState} (hs : CSOk P s) {q i : w32} {c : Copy} (hc : CCopyOk P q i c) :
    CSOk P (s.setInst q i c) := by
  intro q' i' cp h
  simp only [RState.setInst] at h
  split at h
  · rename_i e; obtain ⟨rfl, rfl⟩ := e; cases h; exact hc
  · exact hs q' i' cp h

theorem CSOk.of_inst {s s' : RState} (hs : CSOk P s) (h : s'.inst = s.inst) : CSOk P s' := by
  intro q i cp hc; rw [h] at hc; exact hs q i cp hc

theorem COOk.nil : COOk P [] := by simp [COOk]
theorem COOk.append {a b : List Out} (ha : COOk P a) (hb : COOk P b) : COOk P (a ++ b) := by
  intro x hx; rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h
theorem COOk.ext {x : Ext} : COOk P [.ext x] := by simp [COOk]

theorem COOk.ofSendTo {q : w32} {m : Msg} {x : Out} (h : sendTo q m = some x) (hm : CMOk P m) :
    COOk P [x] := by
  obtain ⟨d, rfl⟩ := sendTo_some h
  intro y hy; rw [List.mem_singleton.1 hy]; exact hm

theorem COOk.ofSendPeer {s : RState} {q : w32} {m : Msg} {x : Out} (h : sendPeer s q m = some x)
    (hm : CMOk P m) : COOk P [x] := by
  unfold sendPeer at h; split at h
  · cases h
  · exact COOk.ofSendTo h hm

theorem COOk.ofBcast {s : RState} {m : Msg} {r : List Out} (h : bcast s m = some r) (hm : CMOk P m) :
    COOk P r := by
  intro y hy
  obtain ⟨q, -, hq⟩ := mapM_some_mem h y hy
  unfold sendPeer at hq; split at hq
  · cases hq
  · obtain ⟨d, rfl⟩ := sendTo_some hq; exact hm

theorem COOk.ofMapSendTo {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendTo q m) = some r) (hm : CMOk P m) : COOk P r := by
  intro y hy
  obtain ⟨q, -, hq⟩ := mapM_some_mem h y hy
  obtain ⟨d, rfl⟩ := sendTo_some hq; exact hm

theorem COOk.ofMapSendPeer {s : RState} {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendPeer s q m) = some r) (hm : CMOk P m) : COOk P r := by
  intro y hy
  obtain ⟨q, -, hq⟩ := mapM_some_mem h y hy
  unfold sendPeer at hq; split at hq
  · cases hq
  · obtain ⟨d, rfl⟩ := sendTo_some hq; exact hm

theorem shortCircuit_cok {s s' : RState} {n : w32} {v : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n v f = some (s', o)) : s'.inst = s.inst ∧ COOk P o := by
  unfold shortCircuit at h
  opeel h
  all_goals
    cases h
    refine forIn_opt_inv _ _ _ (fun p : RState × List Out => p.1.inst = s.inst ∧ COOk P p.2)
      ⟨rfl, COOk.nil⟩ ?_ _ ‹_›
    intro a b st hb hf
    opeel hf
    all_goals (cases hf; first
      | exact hb
      | exact ⟨hb.1, COOk.append hb.2 COOk.ext⟩)

theorem shortCircuit_ite_cok {s s' : RState} {c : Prop} [Decidable c] {n : w32} {v : ValTag}
    {f : Bool} {o : List Out}
    (h : (if c then shortCircuit s n v f else some (s, [])) = some (s', o)) :
    s'.inst = s.inst ∧ COOk P o := by
  split at h
  · exact shortCircuit_cok h
  · cases h; exact ⟨rfl, COOk.nil⟩

theorem COOk.noEP {r : List Out} (h : ∀ x ∈ r, match x with | .send _ m => CMOk P m | .ext _ => True) :
    COOk P r := h

end

/-! ## The handlers -/

set_option hygiene false in
/-- Close `P q i X.cmds` from the hypotheses: the message's commands, `[]`, or an old copy's
(or its recovery candidate's) commands. -/
macro "cok_cmds" : tactic => `(tactic| (
  try simp only [riOf] at *
  first
    | assumption
    | exact h0 _ _
    | exact hlb0 _ ‹_›
    | exact (hs _ _ _ ‹s.inst _ _ = some _›).1
    | exact (hs _ _ _ ‹s.inst _ _ = some _›).2 _ _ ‹_› ‹_›
    | (subst_vars; first
        | assumption
        | exact h0 _ _
        | exact (hs _ _ _ ‹s.inst _ _ = some _›).1
        | exact (hs _ _ _ ‹s.inst _ _ = some _›).2 _ _ ‹_› ‹_›)))

set_option hygiene false in
/-- `CCopyOk P q i c` for a copy built from the message, `[]`, or an old copy. -/
macro "cok_copy" : tactic => `(tactic| (first
  | exact hs _ _ _ ‹s.inst _ _ = some _›
  | (refine ⟨?_, fun lb ir hlb hir => ?_⟩
     · cok_cmds
     · try simp only at hlb
       first
         | (cases hlb; done)
         | exact (hs _ _ _ ‹s.inst _ _ = some _›).2 lb ir hlb hir
         | (cases hlb; try simp only at hir
            first
              | (cases hir; done)
              | (cases hir; cok_cmds)
              | cok_cmds))))

set_option hygiene false in
/-- `CSOk P s'` for a state built from `s` by `setInst`s and frame updates. -/
macro "cok_sok" : tactic => `(tactic| (
  intro q i cp hcp
  try simp only [RState.setInst, updateConflicts_inst, overwrite_inst, RState.setCrt] at hcp
  try (rw [updateCommitted_inst ‹updateCommitted _ _ = some _›] at hcp)
  try (rw [(shortCircuit_cok (P := P) ‹shortCircuit _ _ _ _ = some _›).1] at hcp)
  try (rw [(shortCircuit_ite_cok (P := P) ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›).1] at hcp)
  try simp only [RState.setInst, updateConflicts_inst, overwrite_inst, RState.setCrt] at hcp
  repeat' (split at hcp)
  all_goals first
    | exact hs _ _ _ hcp
    | (cases hcp
       rename_i hqi
       obtain ⟨rfl, rfl⟩ := hqi
       cok_copy)))

set_option hygiene false in
macro "cok_out" : tactic => `(tactic| (first
  | exact COOk.nil
  | exact COOk.ext
  | (apply COOk.ofSendPeer ‹sendPeer _ _ _ = some _›; first | trivial | (simp only [CMOk]; cok_cmds))
  | (apply COOk.ofSendTo ‹sendTo _ _ = some _›; first | trivial | (simp only [CMOk]; cok_cmds))
  | (apply COOk.ofBcast ‹bcast _ _ = some _›; first | trivial | (simp only [CMOk]; cok_cmds))
  | (apply COOk.ofBcast ‹bcastPreAccept _ _ _ _ _ _ _ _ = some _›; simp only [CMOk]; cok_cmds)
  | (apply COOk.ofBcast ‹bcastAccept _ _ _ _ _ _ _ _ = some _›; simp only [CMOk]; cok_cmds)
  | (apply COOk.ofBcast ‹bcastCommit _ _ _ _ _ _ _ = some _›; simp only [CMOk]; cok_cmds)
  | (apply COOk.ofBcast ‹bcastPrepare _ _ _ _ = some _›; trivial)
  | (apply COOk.ofMapSendTo ‹List.mapM _ _ = some _›; trivial)
  | (apply COOk.ofMapSendPeer ‹List.mapM _ _ = some _›; trivial)
  | (apply COOk.append (shortCircuit_cok ‹shortCircuit _ _ _ _ = some _›).2; first | exact COOk.ext | exact COOk.nil)
  | (apply COOk.append (shortCircuit_ite_cok ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›).2
     first | exact COOk.ext | exact COOk.nil)
  | exact (shortCircuit_cok ‹shortCircuit _ _ _ _ = some _›).2
  | exact (shortCircuit_ite_cok ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›).2))

section
variable {P : w32 → w32 → List Cmd → Prop}

theorem stepPreAccept_cok {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s)
    (hm : P m.replica m.inst m.cmds) : CSOk P s' ∧ COOk P o := by
  unfold stepPreAccept at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem stepAccept_cok {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s)
    (hm : P m.replica m.inst m.cmds) : CSOk P s' ∧ COOk P o := by
  unfold stepAccept at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem stepPrepare_cok {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepPrepare at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals (try simp only [‹slt _ _ = true›, if_true] at *)
  all_goals (try simp only [‹¬slt _ _ = true›, if_false, Bool.false_eq_true] at *)
  all_goals first | exact hs | cok_sok | cok_out

theorem stepRecover_cok {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepRecover at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem startPhase1_cok {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o)) (h0 : ∀ q i, P q i [])
    (hs : CSOk P s) (hc : P q i cs) : CSOk P s' ∧ COOk P o := by
  unfold startPhase1 at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem leaderCommit_cok {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit s q i c lb = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s)
    (hc : P q i c.cmds) (hlb0 : ∀ ir, lb.recoveryInst = some ir → P q i ir.cmds) :
    CSOk P s' ∧ COOk P o := by
  unfold leaderCommit at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

set_option hygiene false in
macro "cok_lc" : tactic => `(tactic| (
  exact leaderCommit_cok h h0 (by first | exact hs | cok_sok) (by cok_cmds)
    (fun ir hir => by cok_cmds)))

theorem stepPreAcceptReply_cok {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepPreAcceptReply at h
  peel h
  all_goals first
    | (cases h; refine ⟨?_, ?_⟩ <;> first | exact hs | cok_sok | cok_out)
    | cok_lc

theorem stepPreAcceptOK_cok {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepPreAcceptOK at h
  peel h
  all_goals first
    | (cases h; refine ⟨?_, ?_⟩ <;> first | exact hs | cok_sok | cok_out)
    | cok_lc

theorem stepAcceptReply_cok {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepAcceptReply at h
  peel h
  all_goals first
    | (cases h; refine ⟨?_, ?_⟩ <;> first | exact hs | cok_sok | cok_out)
    | cok_lc

theorem stepCommit_cok {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s)
    (hm : P m.replica m.inst m.cmds) : CSOk P s' ∧ COOk P o := by
  unfold stepCommit at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

set_option maxHeartbeats 4000000 in
theorem stepPrepareReply_cok {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s)
    (hm : P m.replica m.inst m.cmds) : CSOk P s' ∧ COOk P o := by
  unfold stepPrepareReply at h
  peel h
  all_goals first
    | (cases h; refine ⟨?_, ?_⟩ <;> first | exact hs | cok_sok | cok_out)
    | (exact startPhase1_cok h h0 (by cok_sok) (by cok_cmds))


theorem handleExecuted_cok {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold handleExecuted at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem stepExecuteOverwrite_cok {s s' : RState} {m : ExecuteOverwriteM} {o : List Out}
    (h : stepExecuteOverwrite s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepExecuteOverwrite at h
  peel h
  all_goals first
    | (cases h; refine ⟨?_, ?_⟩ <;> first | exact hs | cok_sok | cok_out)
    | exact handleExecuted_cok h h0 (CSOk.of_inst hs (overwrite_inst _ _ _))

theorem stepExec_cok {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepExec at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem stepRead1Reply_cok {s s' : RState} {m : Read1ReplyM} {o : List Out}
    (h : stepRead1Reply s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepRead1Reply at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem stepRead2Reply_cok {s s' : RState} {m : Read2ReplyM} {o : List Out}
    (h : stepRead2Reply s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepRead2Reply at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem stepRead1_cok {s s' : RState} {m : Read1ProxiedM} {o : List Out}
    (h : stepRead1 s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepRead1 at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem stepRead2_cok {s s' : RState} {m : Read2ProxiedM} {o : List Out}
    (h : stepRead2 s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepRead2 at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem stepWrite2_cok {s s' : RState} {m : Write2ProxiedM} {o : List Out}
    (h : stepWrite2 s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepWrite2 at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem stepWrite1_cok {s s' : RState} {m : Write1ProxiedM} {o : List Out}
    (h : stepWrite1 s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepWrite1 at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem stepWrite1Reply_cok {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepWrite1Reply at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem stepWrite2Reply_cok {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (h : stepWrite2Reply s m = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepWrite2Reply at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem stepClientWrite_cok {s s' : RState} {rid cid : w32} {k v : w64} {d : Dep} {o : List Out}
    (h : stepClientWrite s rid cid k v d = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepClientWrite at h
  peel h
  all_goals (cases h; refine ⟨?_, ?_⟩)
  all_goals first | exact hs | cok_sok | cok_out

theorem stepClientRead_cok {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {o : List Out}
    (h : stepClientRead s rid cid k d = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s) :
    CSOk P s' ∧ COOk P o := by
  unfold stepClientRead at h
  peel h
  cases h
  have hx := ‹forIn _ _ _ = Except.ok s'›
  have hm := ‹List.mapM _ _ = some o›
  have hP : s'.inst = s.inst := by
    refine forIn_exc_inv _ _ _ (fun x : RState => x.inst = s.inst) ?_ ?_ _ hx
    · rfl
    intro a b st hb hf
    peel hf
    all_goals (cases hf; exact hb)
  exact ⟨CSOk.of_inst hs hP, COOk.ofMapSendPeer hm trivial⟩

theorem stepClientRMW_cok {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    {o : List Out} (h : stepClientRMW s rid cid k d a b = .ok (s', o)) (h0 : ∀ q i, P q i [])
    (hs : CSOk P s) (hsrc : ∀ cs, cs.head? = some { op := opCAS, k, v := b, oldV := a } →
      P s.id (s.crt s.id) cs) : CSOk P s' ∧ COOk P o := by
  unfold stepClientRMW at h
  peel h
  obtain ⟨-, -, h⟩ := handlePropose_ok h; unfold handleProposeBody at h
  refine startPhase1_cok h h0 (CSOk.of_inst hs (by simp [RState.setCrt])) ?_
  exact hsrc _ rfl

/-- **The commands invariant, per step.** -/
theorem step_cok {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) (h0 : ∀ q i, P q i []) (hs : CSOk P s)
    (hm : ∀ m, e.recv = some m → CMOk P m)
    (hsrc : ∀ rid cid k d a b, e = .rmw rid cid k d a b → ∀ cs,
      cs.head? = some { op := opCAS, k, v := b, oldV := a } → P s.id (s.crt s.id) cs) :
    CSOk P s' ∧ COOk P o := by
  cases e with
  | read => exact stepClientRead_cok h h0 hs
  | write => exact stepClientWrite_cok h h0 hs
  | rmw rid cid k d a b => exact stepClientRMW_cok h h0 hs (hsrc rid cid k d a b rfl)
  | forceWrite => cases h; exact ⟨hs, COOk.nil⟩
  | recover => exact stepRecover_cok h h0 hs
  | exec => exact stepExec_cok h h0 hs
  | msg m =>
    have hm' := hm m rfl
    cases m with
    | read1 => exact stepRead1_cok h h0 hs
    | read2 => exact stepRead2_cok h h0 hs
    | write1 => exact stepWrite1_cok h h0 hs
    | write2 => exact stepWrite2_cok h h0 hs
    | read1Reply => exact stepRead1Reply_cok h h0 hs
    | read2Reply => exact stepRead2Reply_cok h h0 hs
    | write1Reply => exact stepWrite1Reply_cok h h0 hs
    | write2Reply => exact stepWrite2Reply_cok h h0 hs
    | prepare => exact stepPrepare_cok h h0 hs
    | preAccept => exact stepPreAccept_cok h h0 hs hm'
    | accept => exact stepAccept_cok h h0 hs hm'
    | commit => exact stepCommit_cok h h0 hs hm'
    | prepareReply => exact stepPrepareReply_cok h h0 hs hm'
    | preAcceptReply => exact stepPreAcceptReply_cok h h0 hs
    | preAcceptOK => exact stepPreAcceptOK_cok h h0 hs
    | acceptReply => exact stepAcceptReply_cok h h0 hs
    | executed => exact handleExecuted_cok h h0 hs
    | executeOverwrite => exact stepExecuteOverwrite_cok h h0 hs

end

end Perennial.gryff.pure

namespace Perennial.gryff.pure

open model kahn proto

/-! ## Over runs -/

/-- The allowed batches of instance `(q, i)` in run `L`: `[]` or headed by the command of the
RMW of `L` whose instance it is. -/
def PL (L : List Label) (q i : w32) (cs : List Cmd) : Prop :=
  ∀ c0 rest, cs = c0 :: rest → ∃ o ∈ ops L, o.inp = .cas c0.oldV c0.v ∧ rmwInst L o = (q, i)

theorem PL_nil (L : List Label) (q i : w32) : PL L q i [] := fun _ _ h => by cases h

/-- The commands invariant of a configuration (for the run `L` it is a prefix of). -/
def CInv (L : List Label) (c : Cfg gNet) : Prop :=
  ∀ j : Fin 3, CSOk (PL L) (stR c j) ∧ ∀ m ∈ infR c j, CMOk (PL L) m

theorem mem_sentR {j : Fin 3} {o : List Out} {m : Msg} (h : m ∈ sentR j o) :
    ∃ d, Out.send d m ∈ o := by
  unfold sentR at h
  obtain ⟨x, hx, hm⟩ := List.mem_filterMap.1 h
  cases x with
  | send d m' =>
    simp only at hm; split at hm
    · cases hm; exact ⟨d, hx⟩
    · cases hm
  | ext _ => cases hm

/-- The state of a run's configuration is the cut's. -/
theorem grun_st {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3) :
    stR c r = cutSt l l.length r := by
  obtain ⟨cn, h1, h2, h3⟩ := grun_cut h l.length
  have h2' := grun_of_eq (List.drop_length (l := l)) h2
  cases h2'
  obtain ⟨o, ho⟩ := h3 r
  unfold cutSt; rw [stOf_of_runP ho]; rfl

theorem cinv_step {L l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {x : List Ext}
    (h : GRun (Cfg.init gNet) l c) (hi : CInv L c) (hs : GStep c i e c' x)
    (hpre : l ++ [(i, e)] <+: L) : CInv L c' := by
  obtain ⟨s', o, hst⟩ := StepAt.of h hs
  have hsrc : ∀ rid cid k d a b, e = .rmw rid cid k d a b → ∀ cs,
      cs.head? = some { op := opCAS, k, v := b, oldV := a } →
      PL L (stR c i).id ((stR c i).crt (stR c i).id) cs := by
    intro rid cid k d a b he cs hcs c0 rest hc
    subst he hc
    simp only [List.head?_cons, Option.some.injEq] at hcs
    subst hcs
    obtain ⟨L2, hL⟩ := hpre
    have hn : L[l.length]? = some (i, .rmw rid cid k d a b) := by
      rw [← hL]; simp
    have hg : l.length < L.length := (List.getElem?_eq_some_iff.1 hn).1
    have htake : L.take l.length = l := by rw [← hL]; simp
    let o : Op := { g := l.length, r := i, j := (projR (L.take l.length) i).length, cid, rid,
                    inp := .cas a b }
    have hop : opAt L l.length = some o := by unfold opAt; rw [hn]; rfl
    refine ⟨o, mem_ops.2 ⟨hg, hop⟩, rfl, ?_⟩
    have hid : (stR c i).id = rid32 i := (winv h).1.id i
    have hs1 : stR c i = stOf i ((projR L i).take o.j) := by
      rw [grun_st h i]; unfold cutSt
      have : (projR L i).take o.j = projR l i := by
        show (projR L i).take (projR (L.take l.length) i).length = _
        rw [htake]
        conv => lhs; rw [← hL]
        rw [proj_append, proj_append, List.append_assoc, List.take_left' rfl]
      rw [this, List.take_length]
    unfold rmwInst; rw [hid, hs1]
  have key := step_cok hst.ok (PL_nil L) (hi i).1 (fun m hm => (hi i).2 m (hst.recv m hm)) hsrc
  intro j
  refine ⟨?_, fun m hm => ?_⟩
  · rw [hst.st j]
    split
    · exact key.1
    · exact (hi j).1
  · rcases hst.mem hm with hm | hm
    · exact (hi j).2 m hm
    · obtain ⟨d, hd⟩ := mem_sentR hm
      exact key.2 _ hd

theorem cinv_init (L : List Label) : CInv L (Cfg.init gNet) := by
  intro j
  refine ⟨fun q i cp hcp => ?_, fun m hm => by cases hm⟩
  simp [stR, Cfg.init, gNet, RState.init] at hcp

/-- **The commands invariant over runs.** -/
theorem cinv {L : List Label} : ∀ l c, GRun (Cfg.init gNet) l c → l <+: L → CInv L c :=
  grun_inv (fun l c => l <+: L → CInv L c) (fun _ => cinv_init L)
    (fun l c i e c' x h hi hs hpre => cinv_step h (hi ((List.prefix_append l _).trans hpre)) hs hpre)

end Perennial.gryff.pure
