/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/ExFlow.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b (RMW side): **the executed counters' flow** (`LFlow s s'`): the pair
`(numReplicasExecuted, repliedClient)` of an instance's bookkeeping in `s'` is that of the same
instance's bookkeeping in `s`, or `(0, false)` (fresh bookkeeping: `startPhase1`, `stepRecover`) —
for every handler but `handleExecuted` (`handleExecuted_spec`). And **only the executor and the
`ExecuteOverwrite` handler send `ExecuteOverwrite`/`Executed`** (`step_noX`).
-/
module

public import Dsverify.Proof.gryff.PureLb.Heads

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-! ## The counters' flow -/

/-- `v` is the `(numReplicasExecuted, repliedClient)` of instance `(q, i)`'s bookkeeping in `s`. -/
def NumIn (s : RState) (q i : w32) (v : w32 × Bool) : Prop :=
  ∃ c lb, s.inst q i = some c ∧ c.lb = some lb ∧ (lb.numReplicasExecuted, lb.repliedClient) = v

def LFlow (s s' : RState) : Prop := ∀ q i v, NumIn s' q i v → NumIn s q i v ∨ v = (0, false)

/-- Copy `c` at `(q, i)` has `s`'s counters there, or fresh ones. -/
def CN (s : RState) (q i : w32) (c : Copy) : Prop :=
  ∀ lb, c.lb = some lb → NumIn s q i (lb.numReplicasExecuted, lb.repliedClient) ∨
    (lb.numReplicasExecuted, lb.repliedClient) = (0, false)

/-- A bookkeeping whose counters are `s`'s at `(q, i)`, or fresh. -/
def LBN (s : RState) (q i : w32) (lb : LB) : Prop :=
  NumIn s q i (lb.numReplicasExecuted, lb.repliedClient) ∨
    (lb.numReplicasExecuted, lb.repliedClient) = (0, false)

theorem LFlow.rfl' (s : RState) : LFlow s s := fun _ _ _ h => Or.inl h

theorem lflow_setInst {s X : RState} (h : LFlow s X) {q i : w32} {c : Copy} (hc : CN s q i c) :
    LFlow s (X.setInst q i c) := by
  intro q' i' v ⟨c', lb, hc', hlb, hv⟩
  change (if q' = q ∧ i' = i then some c else X.inst q' i') = some c' at hc'
  split at hc'
  · rename_i hqi; obtain ⟨rfl, rfl⟩ := hqi
    cases hc'; subst hv; exact hc lb hlb
  · exact h q' i' v ⟨c', lb, hc', hlb, hv⟩

theorem lflow_same {s X X' : RState} (h : LFlow s X) (h1 : X'.inst = X.inst) : LFlow s X' := by
  intro q i v ⟨c', lb, hc', hlb, hv⟩
  rw [h1] at hc'; exact h q i v ⟨c', lb, hc', hlb, hv⟩

theorem lflow_updC {s X : RState} (h : LFlow s X) (cmds : List Cmd) (q i sq : w32) :
    LFlow s (updateConflicts X cmds q i sq) := lflow_same h (updateConflicts_inst' X cmds q i sq).1

theorem lflow_overwrite {s X : RState} (h : LFlow s X) (v : w64) (t : model.Tag) :
    LFlow s (X.overwrite v t) := lflow_same h (tot.ow_inst ..)

theorem lflow_setCrt {s X : RState} (h : LFlow s X) (q x : w32) : LFlow s (X.setCrt q x) :=
  lflow_same h rfl

theorem lflow_updCommitted' {s X X' : RState} (h : LFlow s X) {q : w32}
    (hu : updateCommitted X q = some X') : LFlow s X' := by
  obtain ⟨cu, rfl⟩ := tot.updateCommitted_form hu
  exact lflow_same h rfl

theorem cn_none {s : RState} {q i : w32} {c : Copy} (h : c.lb = none) : CN s q i c := by
  intro lb hlb; rw [h] at hlb; cases hlb

theorem EqIP.lf {s s' : RState} (h : EqIP s s') : LFlow s s' := lflow_same (LFlow.rfl' s) h.1

macro "lf_fin" : tactic => `(tactic| (
  repeat' (first
    | with_reducible exact LFlow.rfl' _
    | with_reducible assumption
    | (guard_target =~ LFlow _ _
       first
       | with_reducible apply lflow_setInst
       | with_reducible apply lflow_updC
       | with_reducible apply lflow_overwrite
       | with_reducible apply lflow_setCrt
       | (obtain ⟨_, rfl⟩ := tot.updateCommitted_form ‹model.updateCommitted _ _ = some _›)
       | (guard_target =~ LFlow _ (RState.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
          with_reducible apply lflow_same (X := _) _ (by with_reducible rfl)))
    | (guard_target =~ CN _ _ _ _
       first
       | exact cn_none rfl
       | (intro lb hlb
          first
          | (cases hlb; done)
          | (simp only [Option.some.injEq] at hlb; subst hlb
             first
             | exact Or.inr rfl
             | exact Or.inl ⟨_, _, by assumption, by assumption, by rfl⟩
             | exact (by assumption : LBN _ _ _ _))
          | (simp only at hlb
             exact Or.inl ⟨_, _, by assumption, hlb, by rfl⟩)))
    | (guard_target =~ LBN _ _ _ _
       first
       | exact Or.inr rfl
       | exact Or.inl ⟨_, _, by assumption, by assumption, by rfl⟩))))

theorem startPhase1_lf {s0 s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (hX : LFlow s0 s) (h : startPhase1 s q i b ps cs = .ok (s', o)) :
    LFlow s0 s' := by
  unfold startPhase1 at h; peel h
  all_goals (cases h)
  all_goals (refine lflow_updC (lflow_setInst hX ?_) _ _ _ _)
  all_goals (intro lb hlb; simp only [Option.some.injEq] at hlb; subst hlb; exact Or.inr rfl)

theorem leaderCommit_lf {s0 s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (hX : LFlow s0 s) (hps : LBN s0 q i lb)
    (h : leaderCommit s q i c lb = .ok (s', o)) : LFlow s0 s' := by
  have hc1 : CN s0 q i { c with status := St.COMMITTED, lb := some lb } := by
    intro lb' hlb
    simp only [Option.some.injEq] at hlb; subst hlb; exact hps
  unfold leaderCommit at h; peel h
  all_goals (cases h)
  · rename_i _ s1 hu _ _ _
    refine lflow_setInst ?_ (cn_none rfl)
    exact lflow_same (lflow_updCommitted' (lflow_setInst hX hc1) hu) rfl
  · first
    | (rename_i hu _ _; exact lflow_updCommitted' (lflow_setInst hX hc1) hu)
    | (rename_i hu _ _ _ _; exact lflow_updCommitted' (lflow_setInst hX hc1) hu)
    | (rename_i hu _; exact lflow_updCommitted' (lflow_setInst hX hc1) hu)
    | (rename_i hu; exact lflow_updCommitted' (lflow_setInst hX hc1) hu)

theorem cn_same {s X : RState} (h : LFlow s X) {q i : w32} {c0 : Copy}
    (hc : X.inst q i = some c0) {c : Copy} (hlb : c.lb = c0.lb) : CN s q i c := by
  intro lb h1
  rw [hlb] at h1
  exact h q i _ ⟨c0, lb, hc, h1, rfl⟩

macro "lf_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; lf_fin; done)
    | (refine leaderCommit_lf ?_ ?_ $h:ident <;> lf_fin; done)
    | (refine startPhase1_lf ?_ $h:ident <;> lf_fin; done))))

theorem stepPreAccept_lf {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) : LFlow s s' := by
  unfold stepPreAccept at h; peel h
  all_goals (cases h; lf_fin)

theorem stepPreAcceptReply_lf {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) : LFlow s s' := by
  unfold stepPreAcceptReply at h; peel h
  all_goals (first | (cases h; lf_fin; done) | skip)
  all_goals (refine leaderCommit_lf ?_ ?_ h <;> lf_fin)

theorem stepPreAcceptOK_lf {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) : LFlow s s' := by
  unfold stepPreAcceptOK at h; lf_close h

theorem stepAccept_lf {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) : LFlow s s' := by
  unfold stepAccept at h; lf_close h

theorem stepAcceptReply_lf {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) : LFlow s s' := by
  unfold stepAcceptReply at h; lf_close h

theorem stepCommit_lf {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) : LFlow s s' := by
  unfold stepCommit at h; peel h
  all_goals (cases h)
  all_goals (first | exact LFlow.rfl' _ | exact lflow_setCrt (LFlow.rfl' _) _ _ | skip)
  all_goals (refine lflow_updCommitted' ?_ ‹model.updateCommitted _ _ = some _›)
  all_goals (first | refine lflow_updC ?_ _ _ _ _ | skip)
  all_goals (refine lflow_setInst ?_ ?_)
  all_goals (first
    | exact LFlow.rfl' _
    | exact lflow_setCrt (LFlow.rfl' _) _ _
    | exact lflow_same (X := s) (LFlow.rfl' _) rfl
    | exact lflow_same (X := s.setCrt m.replica (m.inst + 1)) (lflow_setCrt (LFlow.rfl' _) _ _) rfl
    | exact cn_none rfl
    | exact cn_same (LFlow.rfl' _) (c0 := ‹Copy›) (by assumption) rfl)

theorem stepPrepare_lf {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) : LFlow s s' := by
  unfold stepPrepare at h; peel h
  all_goals (cases h; refine lflow_setInst (LFlow.rfl' _) ?_)
  all_goals (first
    | exact cn_none rfl
    | (refine cn_same (LFlow.rfl' _) (by assumption) ?_; split <;> rfl)
    | (refine cn_same (LFlow.rfl' _) (by assumption) ?_; rfl))

theorem stepPrepareReply_lf {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) : LFlow s s' := by
  unfold stepPrepareReply at h; lf_close h

theorem stepRecover_lf {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) : LFlow s s' := by
  unfold stepRecover at h; peel h
  all_goals (cases h)
  all_goals (first | exact LFlow.rfl' _ | refine lflow_setInst (LFlow.rfl' _) ?_)
  all_goals (intro lb hlb; simp only [Option.some.injEq] at hlb; subst hlb; exact Or.inr rfl)

theorem stepExec_lf {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) : LFlow s s' := by
  unfold stepExec at h; peel h
  all_goals (cases h)
  all_goals (refine lflow_setInst ?_ (cn_same (LFlow.rfl' _) (c0 := ‹Copy›) (by assumption) rfl))
  all_goals (first | exact LFlow.rfl' _ | exact lflow_same (LFlow.rfl' _) rfl)

/-! ## `handleExecuted` -/

/-- `handleExecuted` on `(q, i)`: nothing (no copy or no bookkeeping), or the counter goes up by
one; it replies (once: `repliedClient`) from the head proposal when the counter reaches 2. -/
theorem handleExecuted_spec {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) :
    (s' = s ∧ o = []) ∨ ∃ c lb b, s.inst m.replica m.inst = some c ∧ c.lb = some lb ∧
      s' = s.setInst m.replica m.inst { c with lb := some { lb with
        numReplicasExecuted := lb.numReplicasExecuted + 1, repliedClient := b } } ∧
      ((o = [] ∧ b = lb.repliedClient ∧
          ¬(lb.repliedClient = false ∧ sge (lb.numReplicasExecuted + 1) 2 = true)) ∨
        (lb.repliedClient = false ∧ sge (lb.numReplicasExecuted + 1) 2 = true ∧ b = true ∧
          ∃ p, lb.clientProposals.head? = some p ∧ o = [.ext (.rmwReply p.client p.cmdId 1)])) := by
  unfold handleExecuted at h; peel h
  all_goals (cases h)
  all_goals (first | exact Or.inl ⟨rfl, rfl⟩ | skip)
  · have hc := ‹(!_ && _) = true›
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hc
    exact Or.inr ⟨_, _, true, ‹_›, ‹_›, rfl, Or.inr ⟨hc.1, hc.2, rfl, _, ‹_›, rfl⟩⟩
  · refine Or.inr ⟨_, _, _, ‹_›, ‹_›, rfl, Or.inl ⟨rfl, rfl, ?_⟩⟩
    have hc := ‹¬(!_ && _) = true›
    intro ⟨h1, h2⟩; apply hc; rw [h1, h2]; rfl

/-! ## `Executed`/`ExecuteOverwrite` messages -/

def isXMsg : Msg → Bool
  | .executed _ => true
  | .executeOverwrite _ => true
  | _ => false

def isXOut : Out → Bool
  | .send _ m => isXMsg m
  | .ext _ => false

/-- No `Executed`/`ExecuteOverwrite` among outputs. -/
def NoX (o : List Out) : Prop := ∀ x ∈ o, isXOut x = false

theorem noX_nil : NoX [] := by simp [NoX]
theorem noX_append {a b : List Out} (ha : NoX a) (hb : NoX b) : NoX (a ++ b) := by
  intro x hx; rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h
theorem noX_single {x : Out} (h : isXOut x = false) : NoX [x] := by
  intro y hy; rw [List.mem_singleton.1 hy]; exact h

theorem sendTo_isX {q : w32} {m : Msg} {x : Out} (h : sendTo q m = some x) : isXOut x = isXMsg m := by
  unfold sendTo at h
  obtain ⟨d, _, rfl⟩ := Option.map_eq_some_iff.1 h; rfl

theorem sendPeer_isX {s : RState} {q : w32} {m : Msg} {x : Out} (h : sendPeer s q m = some x) :
    isXOut x = isXMsg m := by
  unfold sendPeer at h; split at h
  · cases h
  · exact sendTo_isX h

theorem mapM_sendTo_noX {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendTo q m) = some r) (hm : isXMsg m = false) : NoX r := by
  intro y hy
  obtain ⟨a, _, h'⟩ := mapM_some_mem h y hy
  rw [sendTo_isX h']; exact hm

theorem mapM_sendPeer_noX {s : RState} {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendPeer s q m) = some r) (hm : isXMsg m = false) : NoX r := by
  intro y hy
  obtain ⟨a, _, h'⟩ := mapM_some_mem h y hy
  rw [sendPeer_isX h']; exact hm

theorem bcast_noX {s : RState} {m : Msg} {r : List Out} (h : bcast s m = some r)
    (hm : isXMsg m = false) : NoX r := mapM_sendPeer_noX h hm

theorem bcastPreAccept_noX {s : RState} {a b c : w32} {cs : List Cmd} {sq : w32} {d : Deps}
    {v : ValTag} {r : List Out} (h : bcastPreAccept s a b c cs sq d v = some r) : NoX r :=
  bcast_noX h rfl
theorem bcastAccept_noX {s : RState} {a b c : w32} {cs : List Cmd} {sq : w32} {d : Deps}
    {v : ValTag} {r : List Out} (h : bcastAccept s a b c cs sq d v = some r) : NoX r :=
  bcast_noX h rfl
theorem bcastCommit_noX {s : RState} {a b : w32} {cs : List Cmd} {sq : w32} {d : Deps}
    {v : ValTag} {r : List Out} (h : bcastCommit s a b cs sq d v = some r) : NoX r :=
  bcast_noX h rfl
theorem bcastPrepare_noX {s : RState} {a b c : w32} {r : List Out}
    (h : bcastPrepare s a b c = some r) : NoX r :=
  bcast_noX h rfl

theorem shortCircuit_noX {s s' : RState} {n : w32} {v : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n v f = some (s', o)) : NoX o := by
  obtain ⟨_, _, -, -, -, -, hsco⟩ := shortCircuit_spec h
  intro x hx
  obtain ⟨_, _, rfl, -⟩ := hsco x hx
  rfl

macro "nx_fin" : tactic => `(tactic| (first
  | exact noX_nil
  | exact noX_single rfl
  | with_reducible exact bcastPreAccept_noX ‹_›
  | with_reducible exact bcastAccept_noX ‹_›
  | with_reducible exact bcastCommit_noX ‹_›
  | with_reducible exact bcastPrepare_noX ‹_›
  | (rw [noX_single (by rw [sendPeer_isX ‹sendPeer _ _ _ = some _›]; rfl)]; done)
  | exact noX_single (by rw [sendPeer_isX ‹sendPeer _ _ _ = some _›]; rfl)
  | exact noX_single (by rw [sendTo_isX ‹sendTo _ _ = some _›]; rfl)
  | with_reducible exact mapM_sendTo_noX ‹_› rfl
  | with_reducible exact mapM_sendPeer_noX ‹_› rfl
  | exact noX_append (shortCircuit_noX ‹shortCircuit _ _ _ _ = some _›) (noX_single rfl)
  | exact noX_append noX_nil (noX_single rfl)
  | exact shortCircuit_noX ‹shortCircuit _ _ _ _ = some _›))

theorem startPhase1_noX {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o)) : NoX o := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; nx_fin)

theorem leaderCommit_noX {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit s q i c lb = .ok (s', o)) : NoX o := by
  unfold leaderCommit at h; peel h
  all_goals (cases h; nx_fin)

macro "nx_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; nx_fin; done)
    | exact leaderCommit_noX $h:ident
    | exact startPhase1_noX $h:ident)))

/-- The executor and the `Executed`/`ExecuteOverwrite` handlers. -/
def Ev.xspecial : Ev → Bool
  | .exec _ _ => true
  | .msg (.executed _) => true
  | .msg (.executeOverwrite _) => true
  | _ => false

set_option maxHeartbeats 4000000 in
theorem step_noX {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) (he : Ev.xspecial e = false) : NoX o := by
  cases e with
  | read =>
    obtain ⟨-, -, -, -, -, ho⟩ := stepClientRead_spec' h
    intro x hx; obtain ⟨dd, rfl, -⟩ := ho x hx; rfl
  | write =>
    obtain ⟨-, -, -, -, -, m0, -, -, -, rfl⟩ := stepClientWrite_spec h
    intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> rfl
  | rmw =>
    change stepClientRMW _ _ _ _ _ _ _ = _ at h
    unfold stepClientRMW at h; peel h; replace h := (handlePropose_ok h).2.2; unfold handleProposeBody at h
    exact startPhase1_noX h
  | forceWrite => cases h; exact noX_nil
  | recover => change stepRecover _ _ _ = _ at h; unfold stepRecover at h; nx_close h
  | exec => cases he
  | msg m =>
    cases m with
    | read1 => change stepRead1 _ _ = _ at h; unfold stepRead1 at h; nx_close h
    | read2 => change stepRead2 _ _ = _ at h; unfold stepRead2 at h; nx_close h
    | write1 => change stepWrite1 _ _ = _ at h; unfold stepWrite1 at h; nx_close h
    | write2 => change stepWrite2 _ _ = _ at h; unfold stepWrite2 at h; nx_close h
    | read1Reply => change stepRead1Reply _ _ = _ at h; unfold stepRead1Reply at h; nx_close h
    | read2Reply => change stepRead2Reply _ _ = _ at h; unfold stepRead2Reply at h; nx_close h
    | write1Reply => change stepWrite1Reply _ _ = _ at h; unfold stepWrite1Reply at h; nx_close h
    | write2Reply =>
      change stepWrite2Reply _ _ = _ at h; unfold stepWrite2Reply at h; peel h
      all_goals (cases h)
      all_goals (first
        | nx_fin
        | (rcases oite_some_iff.1 ‹(if _ then shortCircuit _ _ _ _ else some _) = some _› with
             ⟨-, hsc⟩ | ⟨-, hsc⟩
           · exact noX_append (shortCircuit_noX hsc) (noX_single rfl)
           · cases hsc; exact noX_append noX_nil (noX_single rfl)))
    | prepare => change stepPrepare _ _ = _ at h; unfold stepPrepare at h; nx_close h
    | preAccept => change stepPreAccept _ _ = _ at h; unfold stepPreAccept at h; nx_close h
    | accept => change stepAccept _ _ = _ at h; unfold stepAccept at h; nx_close h
    | commit => change stepCommit _ _ = _ at h; unfold stepCommit at h; nx_close h
    | prepareReply => change stepPrepareReply _ _ = _ at h; unfold stepPrepareReply at h; nx_close h
    | preAcceptReply =>
      change stepPreAcceptReply _ _ = _ at h; unfold stepPreAcceptReply at h; nx_close h
    | preAcceptOK => change stepPreAcceptOK _ _ = _ at h; unfold stepPreAcceptOK at h; nx_close h
    | acceptReply => change stepAcceptReply _ _ = _ at h; unfold stepAcceptReply at h; nx_close h
    | executed => cases he
    | executeOverwrite => cases he

theorem stepClientRMW_lf {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    {o : List Out} (h : stepClientRMW s rid cid k d a b = .ok (s', o)) : LFlow s s' := by
  unfold stepClientRMW at h
  peel h
  replace h := (handlePropose_ok h).2.2; unfold handleProposeBody at h
  intro q i v hv
  rcases startPhase1_lf (LFlow.rfl' _) h q i v hv with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

set_option maxHeartbeats 4000000 in
/-- The counters' flow of every step but `handleExecuted`'s (direct or after an
`ExecuteOverwrite` to self). -/
theorem step_lflow {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) (he : Ev.mspecial e = false) : LFlow s s' := by
  cases e with
  | read => exact (stepClientRead_eqip h).lf
  | write => exact (stepClientWrite_eqip h).lf
  | rmw => exact stepClientRMW_lf h
  | forceWrite => cases h; exact LFlow.rfl' _
  | recover => exact stepRecover_lf h
  | exec => exact stepExec_lf h
  | msg m =>
    cases m with
    | read1 => exact (stepRead1_eqip h).lf
    | read2 => exact (stepRead2_eqip h).lf
    | write1 => exact (stepWrite1_eqip h).lf
    | write2 => exact (stepWrite2_eqip h).lf
    | read1Reply => exact (stepRead1Reply_eqip h).lf
    | read2Reply => exact (stepRead2Reply_eqip h).lf
    | write1Reply => exact (stepWrite1Reply_eqip h).lf
    | write2Reply => exact (stepWrite2Reply_eqip h).lf
    | prepare => exact stepPrepare_lf h
    | preAccept => exact stepPreAccept_lf h
    | accept => exact stepAccept_lf h
    | commit => exact stepCommit_lf h
    | prepareReply => exact stepPrepareReply_lf h
    | preAcceptReply => exact stepPreAcceptReply_lf h
    | preAcceptOK => exact stepPreAcceptOK_lf h
    | acceptReply => exact stepAcceptReply_lf h
    | executed => cases he
    | executeOverwrite => cases he

end Perennial.gryff.pure
