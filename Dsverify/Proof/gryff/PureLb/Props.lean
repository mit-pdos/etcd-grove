/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/Props.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b (the RMW side, in progress): **client proposals flow** (`PFlow s s'`: every proposal in
`s'` — its proposal queue or any copy's bookkeeping — was in `s`), for the EPaxos handlers; the
base of the proposal-ownership invariant (every proposal at `R` is owned by an RMW at `R`).
-/
module

public import Dsverify.Proof.gryff.PureLb.RInv
public import Dsverify.Proof.gryff.PureT.EpSteps

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-- `p` is a proposal of state `s`: queued, or in a copy's bookkeeping. -/
def PropIn (s : RState) (p : Proposal) : Prop :=
  p ∈ s.proposeQ ∨ ∃ q i c lb, s.inst q i = some c ∧ c.lb = some lb ∧ p ∈ lb.clientProposals

/-- `s'`'s proposals are `s`'s. -/
def PFlow (s s' : RState) : Prop := ∀ p, PropIn s' p → PropIn s p

/-- A list of proposals of `s`. -/
def LBIn (s : RState) (L : List Proposal) : Prop := ∀ p ∈ L, PropIn s p

/-- A copy's proposals are `s`'s. -/
def CIn (s : RState) (c : Copy) : Prop :=
  ∀ lb, c.lb = some lb → ∀ p ∈ lb.clientProposals, PropIn s p

theorem PFlow.rfl' (s : RState) : PFlow s s := fun _ h => h

theorem pflow_setInst {s X : RState} (h : PFlow s X) {q i : w32} {c : Copy} (hc : CIn s c) :
    PFlow s (X.setInst q i c) := by
  intro p hp
  rcases hp with hp | ⟨q', i', c', lb, hc', hlb, hp⟩
  · exact h p (Or.inl hp)
  · change (if q' = q ∧ i' = i then some c else X.inst q' i') = some c' at hc'
    split at hc'
    · cases hc'; exact hc lb hlb p hp
    · exact h p (Or.inr ⟨q', i', c', lb, hc', hlb, hp⟩)

theorem pflow_same {s X X' : RState} (h : PFlow s X) (h1 : X'.inst = X.inst)
    (h2 : X'.proposeQ = X.proposeQ) : PFlow s X' := by
  intro p hp
  rcases hp with hp | ⟨q', i', c', lb, hc', hlb, hp⟩
  · rw [h2] at hp; exact h p (Or.inl hp)
  · rw [h1] at hc'; exact h p (Or.inr ⟨q', i', c', lb, hc', hlb, hp⟩)

theorem pflow_append {s X : RState} (h : PFlow s X) {L : List Proposal}
    (hL : ∀ p ∈ L, PropIn s p) {X' : RState} (h1 : X'.inst = X.inst)
    (h2 : X'.proposeQ = X.proposeQ ++ L) : PFlow s X' := by
  intro p hp
  rcases hp with hp | ⟨q', i', c', lb, hc', hlb, hp⟩
  · rw [h2, List.mem_append] at hp
    rcases hp with hp | hp
    · exact h p (Or.inl hp)
    · exact hL p hp
  · rw [h1] at hc'; exact h p (Or.inr ⟨q', i', c', lb, hc', hlb, hp⟩)

theorem pflow_drop {s X : RState} (h : PFlow s X) {k : Nat} {X' : RState}
    (h1 : X'.inst = X.inst) (h2 : X'.proposeQ = X.proposeQ.drop k) : PFlow s X' := by
  intro p hp
  rcases hp with hp | ⟨q', i', c', lb, hc', hlb, hp⟩
  · rw [h2] at hp; exact h p (Or.inl (List.mem_of_mem_drop hp))
  · rw [h1] at hc'; exact h p (Or.inr ⟨q', i', c', lb, hc', hlb, hp⟩)

theorem propIn_of_inst {s X : RState} (h : PFlow s X) {q i : w32} {c : Copy} {lb : LB}
    (hc : X.inst q i = some c) (hlb : c.lb = some lb) {p : Proposal}
    (hp : p ∈ lb.clientProposals) : PropIn s p :=
  h p (Or.inr ⟨q, i, c, lb, hc, hlb, hp⟩)

theorem cin_none {s : RState} {c : Copy} (h : c.lb = none) : CIn s c := by
  intro lb hlb; rw [h] at hlb; cases hlb

theorem cin_of {s X : RState} (h : PFlow s X) {q i : w32} {c0 : Copy} (hc : X.inst q i = some c0)
    {c : Copy} (hlb : ∀ lb, c.lb = some lb → ∃ lb0, c0.lb = some lb0 ∧
      lb.clientProposals = lb0.clientProposals) : CIn s c := by
  intro lb h1 p hp
  obtain ⟨lb0, h2, h3⟩ := hlb lb h1
  rw [h3] at hp
  exact propIn_of_inst h hc h2 hp

theorem cin_of' {s X : RState} (h : PFlow s X) {q i : w32} {c0 : Copy} (hc : X.inst q i = some c0)
    {lb0 : LB} (hlb0 : c0.lb = some lb0) {c : Copy}
    (hlb : ∀ lb, c.lb = some lb → lb.clientProposals = lb0.clientProposals) : CIn s c :=
  cin_of h hc (fun lb h1 => ⟨lb0, hlb0, hlb lb h1⟩)

theorem updateConflicts_inst' (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).inst = s.inst ∧
      (updateConflicts s cmds q i sq).proposeQ = s.proposeQ := by
  obtain ⟨cf, ms, he, -⟩ := tot.updateConflicts_eq s cmds q i sq
  rw [he]; exact ⟨rfl, rfl⟩

theorem pflow_updC {s X : RState} (h : PFlow s X) (cmds : List Cmd) (q i sq : w32) :
    PFlow s (updateConflicts X cmds q i sq) :=
  pflow_same h (updateConflicts_inst' X cmds q i sq).1 (updateConflicts_inst' X cmds q i sq).2

theorem pflow_updCommitted {s X X' : RState} (h : PFlow s X) {q : w32}
    (hu : updateCommitted X q = some X') : PFlow s X' := by
  obtain ⟨cu, rfl⟩ := tot.updateCommitted_form hu
  exact pflow_same h rfl rfl

theorem pflow_overwrite {s X : RState} (h : PFlow s X) (v : w64) (t : model.Tag) :
    PFlow s (X.overwrite v t) := pflow_same h (tot.ow_inst ..) (tot.ow_proposeQ ..)

theorem pflow_setCrt {s X : RState} (h : PFlow s X) (q x : w32) : PFlow s (X.setCrt q x) :=
  pflow_same h rfl rfl

theorem cin_same {s X : RState} (h : PFlow s X) {q i : w32} {c0 : Copy}
    (hc : X.inst q i = some c0) {c : Copy} (hlb : c.lb = c0.lb) : CIn s c := by
  intro lb h1 p hp
  rw [hlb] at h1
  exact propIn_of_inst h hc h1 hp

theorem cin_lit {s : RState} {c : Copy} {L : List Proposal} (hL : ∀ p ∈ L, PropIn s p)
    (hlb : ∀ lb, c.lb = some lb → lb.clientProposals = L) : CIn s c := by
  intro lb h1 p hp
  rw [hlb lb h1] at hp
  exact hL p hp

theorem props_of_inst {s X : RState} (h : PFlow s X) {q i : w32} {c0 : Copy}
    (hc : X.inst q i = some c0) {lb0 : LB} (hlb0 : c0.lb = some lb0) :
    ∀ p ∈ lb0.clientProposals, PropIn s p := fun _ hp => propIn_of_inst h hc hlb0 hp

theorem props_of_inst' {s X : RState} (h : PFlow s X) {q i : w32} {c0 : Copy} {lb0 : LB}
    (hlb0 : c0.lb = some lb0) (hc : X.inst q i = some c0) :
    ∀ p ∈ lb0.clientProposals, PropIn s p := fun _ hp => propIn_of_inst h hc hlb0 hp

/-- Closes `PFlow s E` for a handler's result `E` (and the copies' `CIn` side goals). -/
macro "pf_finl" : tactic => `(tactic| (
  repeat' (first
    | with_reducible exact PFlow.rfl' _
    | with_reducible assumption
    | (guard_target =~ PFlow _ _
       first
       | with_reducible apply pflow_setInst
       | with_reducible apply pflow_updC
       | with_reducible apply pflow_overwrite
       | with_reducible apply pflow_setCrt
       | (obtain ⟨_, rfl⟩ := tot.updateCommitted_form ‹model.updateCommitted _ _ = some _›)
       | (with_reducible refine pflow_append (X := _) ?_ (?_ : LBIn _ _) (by with_reducible rfl) (by with_reducible rfl))
       | (with_reducible refine pflow_drop (X := _) ?_ (by with_reducible rfl) (by with_reducible rfl))
       | (guard_target =~ PFlow _ (RState.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
          with_reducible apply pflow_same (X := _) _ (by with_reducible rfl) (by with_reducible rfl)))
    | (guard_target =~ CIn _ _
       first
       | exact cin_none rfl
       | (refine cin_same (PFlow.rfl' _) ?_ (by split <;> rfl)
          assumption)
       | (intro lb hlb p hp
          simp only [Option.some.injEq] at hlb
          subst hlb
          dsimp only at hp
          split at hp
          · exact props_of_inst' (PFlow.rfl' _) (by assumption) (by assumption) p hp
          · cases hp)
       | (intro lb hlb p hp
          first
          | (cases hlb; done)
          | (simp only [Option.some.injEq] at hlb; subst hlb
             first
             | exact props_of_inst' (PFlow.rfl' _) (by assumption) (by assumption) p (by exact hp)
             | exact (by assumption : LBIn _ _) p (by exact hp))
          | (simp only at hlb
             exact props_of_inst (PFlow.rfl' _) (by assumption) hlb p hp)))
    | (guard_target =~ LBIn _ _
       intro p hp
       exact props_of_inst' (PFlow.rfl' _) (by assumption) (by assumption) p (by exact hp)))))

set_option maxHeartbeats 1000000 in
theorem startPhase1_pfl {s0 s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (hX : PFlow s0 s) (hps : LBIn s0 ps)
    (h : startPhase1 s q i b ps cs = .ok (s', o)) : PFlow s0 s' := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; pf_finl)

theorem leaderCommit_pfl {s0 s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (hX : PFlow s0 s) (hps : LBIn s0 lb.clientProposals)
    (h : leaderCommit s q i c lb = .ok (s', o)) : PFlow s0 s' := by
  have hc1 : CIn s0 { c with status := St.COMMITTED, lb := some lb } := by
    intro lb' hlb p hp
    simp only [Option.some.injEq] at hlb; subst hlb; exact hps p hp
  unfold leaderCommit at h; peel h
  all_goals (cases h)
  · rename_i _ s1 hu _ _ _
    refine pflow_setInst ?_ (cin_none rfl)
    exact pflow_append (pflow_updCommitted (pflow_setInst hX hc1) hu) hps rfl rfl
  · first
    | (rename_i hu _ _; exact pflow_updCommitted (pflow_setInst hX hc1) hu)
    | (rename_i hu _ _ _ _; exact pflow_updCommitted (pflow_setInst hX hc1) hu)
    | (rename_i hu _; exact pflow_updCommitted (pflow_setInst hX hc1) hu)
    | (rename_i hu; exact pflow_updCommitted (pflow_setInst hX hc1) hu)

macro "pf_closel" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; pf_finl; done)
    | (refine leaderCommit_pfl ?_ ?_ $h:ident <;> pf_finl; done)
    | (refine startPhase1_pfl ?_ ?_ $h:ident <;> pf_finl; done))))

theorem handleExecuted_pfl {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) : PFlow s s' := by
  unfold handleExecuted at h; peel h
  all_goals (cases h; pf_finl)

theorem stepPreAccept_pf {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) : PFlow s s' := by
  unfold stepPreAccept at h; peel h
  all_goals (cases h; pf_finl)

theorem stepPreAcceptReply_pfl {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) : PFlow s s' := by
  unfold stepPreAcceptReply at h; peel h
  all_goals (first | (cases h; pf_finl; done) | skip)
  all_goals (refine leaderCommit_pfl ?_ ?_ h <;> pf_finl)

theorem stepPreAcceptOK_pfl {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) : PFlow s s' := by
  unfold stepPreAcceptOK at h; pf_closel h

theorem stepAccept_pf {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) : PFlow s s' := by
  unfold stepAccept at h; pf_closel h

theorem stepAcceptReply_pfl {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) : PFlow s s' := by
  unfold stepAcceptReply at h; pf_closel h

theorem stepCommit_pf {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) : PFlow s s' := by
  unfold stepCommit at h; peel h
  all_goals (cases h)
  all_goals (first | exact PFlow.rfl' _ | exact pflow_setCrt (PFlow.rfl' _) _ _ | skip)
  all_goals (refine pflow_updCommitted ?_ ‹model.updateCommitted _ _ = some _›)
  all_goals (first | refine pflow_updC ?_ _ _ _ _ | skip)
  all_goals (refine pflow_setInst ?_ ?_)
  all_goals (first
    | exact PFlow.rfl' _
    | exact pflow_setCrt (PFlow.rfl' _) _ _
    | exact pflow_append (X := s) (PFlow.rfl' _)
        (props_of_inst' (PFlow.rfl' _) (by assumption) (by assumption)) rfl rfl
    | exact pflow_append (X := s.setCrt m.replica (m.inst + 1)) (pflow_setCrt (PFlow.rfl' _) _ _)
        (props_of_inst' (PFlow.rfl' _) (by assumption) (by assumption)) rfl rfl
    | exact cin_none rfl
    | exact cin_same (PFlow.rfl' _) (c0 := ‹Copy›) ‹_› rfl)

theorem stepPrepare_pfl {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) : PFlow s s' := by
  unfold stepPrepare at h; peel h
  all_goals (cases h; refine pflow_setInst (PFlow.rfl' _) ?_)
  all_goals (first
    | exact cin_none rfl
    | (refine cin_same (PFlow.rfl' _) (by assumption) ?_; split <;> rfl)
    | (refine cin_same (PFlow.rfl' _) (by assumption) ?_; rfl))

theorem stepPrepareReply_pfl {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) : PFlow s s' := by
  unfold stepPrepareReply at h; pf_closel h

theorem stepRecover_pfl {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) : PFlow s s' := by
  unfold stepRecover at h; peel h
  all_goals (cases h)
  all_goals (first | exact PFlow.rfl' _ | refine pflow_setInst (PFlow.rfl' _) ?_)
  all_goals (intro lb hlb p; simp only [Option.some.injEq] at hlb; subst hlb; dsimp only)
  all_goals (first | (split <;> intro hp) | intro hp)
  all_goals (first
    | (cases hp; done)
    | exact props_of_inst' (PFlow.rfl' _) (by assumption) (by assumption) p hp)

theorem stepExec_pf {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) : PFlow s s' := by
  unfold stepExec at h; peel h
  all_goals (cases h)
  all_goals (refine pflow_setInst ?_ (cin_same (PFlow.rfl' _) (c0 := ‹Copy›) ‹_› rfl))
  all_goals (first | exact PFlow.rfl' _ | exact pflow_same (PFlow.rfl' _) rfl rfl)

theorem stepExecuteOverwrite_pfl {s s' : RState} {m : ExecuteOverwriteM} {o : List Out}
    (h : stepExecuteOverwrite s m = .ok (s', o)) : PFlow s s' := by
  unfold stepExecuteOverwrite at h; peel h
  all_goals (first
    | (cases h; exact pflow_overwrite (PFlow.rfl' _) _ _)
    | exact fun p hp => pflow_overwrite (PFlow.rfl' s) m.v m.t p (handleExecuted_pfl h p hp))

/-- Same instances and proposal queue. -/
def EqIP (s s' : RState) : Prop := s'.inst = s.inst ∧ s'.proposeQ = s.proposeQ

theorem EqIP.pf {s s' : RState} (h : EqIP s s') : PFlow s s' := pflow_same (PFlow.rfl' s) h.1 h.2

theorem shortCircuit_eqip {s s' : RState} {n : w32} {v : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n v f = some (s', o)) : EqIP s s' := by
  obtain ⟨X, Y, rfl, -⟩ := shortCircuit_spec h; exact ⟨rfl, rfl⟩

macro "eqip_fin" : tactic => `(tactic| (first
  | exact ⟨rfl, rfl⟩
  | (have hsc := shortCircuit_eqip ‹shortCircuit _ _ _ _ = some _›
     exact ⟨hsc.1, hsc.2⟩)
  | exact ⟨by simp only [tot.ow_inst], by simp only [tot.ow_proposeQ]⟩
  | (split <;> first | exact ⟨rfl, rfl⟩ | exact ⟨by simp only [tot.ow_inst], by simp only [tot.ow_proposeQ]⟩)))

theorem stepRead1Reply_eqip {s s' : RState} {m : Read1ReplyM} {o : List Out}
    (h : stepRead1Reply s m = .ok (s', o)) : EqIP s s' := by
  unfold stepRead1Reply at h; peel h
  all_goals (cases h; eqip_fin)

theorem stepRead2Reply_eqip {s s' : RState} {m : Read2ReplyM} {o : List Out}
    (h : stepRead2Reply s m = .ok (s', o)) : EqIP s s' := by
  unfold stepRead2Reply at h; peel h
  all_goals (cases h; eqip_fin)

theorem stepWrite1Reply_eqip {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) : EqIP s s' := by
  unfold stepWrite1Reply at h; peel h
  all_goals (cases h; eqip_fin)

theorem stepWrite2Reply_eqip {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (h : stepWrite2Reply s m = .ok (s', o)) : EqIP s s' := by
  unfold stepWrite2Reply at h; peel h
  all_goals (cases h)
  all_goals (first
    | exact ⟨rfl, rfl⟩
    | (rcases oite_some_iff.1 ‹(if _ then shortCircuit _ _ _ _ else some _) = some _› with
         ⟨-, hsc⟩ | ⟨-, hsc⟩
       · have := shortCircuit_eqip hsc; exact ⟨this.1, this.2⟩
       · cases hsc; exact ⟨rfl, rfl⟩))

theorem stepRead1_eqip {s s' : RState} {m : Read1ProxiedM} {o : List Out}
    (h : stepRead1 s m = .ok (s', o)) : EqIP s s' := by
  unfold stepRead1 at h; peel h
  all_goals (cases h; eqip_fin)

theorem stepRead2_eqip {s s' : RState} {m : Read2ProxiedM} {o : List Out}
    (h : stepRead2 s m = .ok (s', o)) : EqIP s s' := by
  unfold stepRead2 at h; peel h
  all_goals (cases h; eqip_fin)

theorem stepWrite1_eqip {s s' : RState} {m : Write1ProxiedM} {o : List Out}
    (h : stepWrite1 s m = .ok (s', o)) : EqIP s s' := by
  unfold stepWrite1 at h; peel h
  all_goals (cases h; eqip_fin)

theorem stepWrite2_eqip {s s' : RState} {m : Write2ProxiedM} {o : List Out}
    (h : stepWrite2 s m = .ok (s', o)) : EqIP s s' := by
  unfold stepWrite2 at h; peel h
  all_goals (cases h; eqip_fin)

theorem stepClientWrite_eqip {s s' : RState} {rid cid : w32} {k v : w64} {d : Dep} {o : List Out}
    (h : stepClientWrite s rid cid k v d = .ok (s', o)) : EqIP s s' := by
  obtain ⟨-, -, -, rfl, -⟩ := stepClientWrite_spec' h; exact ⟨rfl, rfl⟩

theorem stepClientRead_eqip {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {o : List Out}
    (h : stepClientRead s rid cid k d = .ok (s', o)) : EqIP s s' := by
  obtain ⟨-, -, -, ⟨X, rfl⟩, -⟩ := stepClientRead_spec' h; exact ⟨rfl, rfl⟩

theorem propIn_aug {s : RState} {P p : Proposal}
    (h : PropIn { s with proposeQ := s.proposeQ ++ [P] } p) : PropIn s p ∨ p = P := by
  rcases h with h | h
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (List.mem_singleton.1 h)
  · exact Or.inl (Or.inr h)

/-- A client RMW adds its own proposal. -/
theorem stepClientRMW_pf {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    {o : List Out} (h : stepClientRMW s rid cid k d a b = .ok (s', o)) :
    ∀ p, PropIn s' p → PropIn s p ∨ (p.client = cid ∧ p.cmdId = rid) := by
  unfold stepClientRMW at h
  peel h
  replace h := (handlePropose_ok h).2.2; unfold handleProposeBody at h
  let P : Proposal := { cmdId := rid, client := cid, cmd := { op := opCAS, k, v := b, oldV := a } }
  let A : RState := { s with proposeQ := s.proposeQ ++ [P] }
  have hA : PFlow A s' := by
    refine startPhase1_pfl ?_ ?_ h
    · intro p hp
      rcases hp with hp | hp
      · exact Or.inl (List.mem_append_left _ (List.mem_of_mem_drop hp))
      · exact Or.inr hp
    · intro p hp
      rcases List.mem_cons.1 hp with hp | hp
      · exact Or.inl (List.mem_append_right _ (List.mem_singleton.2 hp))
      · exact Or.inl (List.mem_append_left _ (List.mem_of_mem_take hp))
  intro p hp
  rcases propIn_aug (hA p hp) with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨by rw [h1], by rw [h1]⟩

end Perennial.gryff.pure
