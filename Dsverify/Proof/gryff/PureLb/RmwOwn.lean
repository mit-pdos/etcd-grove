/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLb/RmwOwn.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-b: **RMW reply ownership**: every client proposal at `R` (queued or in a copy's
bookkeeping) is owned by an RMW operation at `R` (`POwn`, `pown`); an RMW reply is output only by
`handleExecuted` (`rmwReply_src`), from a proposal of the state, hence has an RMW's key.
-/
module

public import Dsverify.Proof.gryff.PureLb.Props

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-! ## Which handlers output RMW replies -/

def isMOut : Out → Bool
  | .ext (.rmwReply ..) => true
  | _ => false

/-- No RMW reply among outputs. -/
def NoM (o : List Out) : Prop := ∀ x ∈ o, isMOut x = false

theorem noM_nil : NoM [] := by simp [NoM]
theorem noM_append {a b : List Out} (ha : NoM a) (hb : NoM b) : NoM (a ++ b) := by
  intro x hx; rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h
theorem noM_single {x : Out} (h : isMOut x = false) : NoM [x] := by
  intro y hy; rw [List.mem_singleton.1 hy]; exact h

theorem sendTo_isM {q : w32} {m : Msg} {x : Out} (h : sendTo q m = some x) : isMOut x = false := by
  unfold sendTo at h
  obtain ⟨d, _, rfl⟩ := Option.map_eq_some_iff.1 h; rfl

theorem sendPeer_isM {s : RState} {q : w32} {m : Msg} {x : Out} (h : sendPeer s q m = some x) :
    isMOut x = false := by
  unfold sendPeer at h; split at h
  · cases h
  · exact sendTo_isM h

theorem mapM_sendTo_noM {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendTo q m) = some r) : NoM r := by
  intro y hy
  obtain ⟨a, _, h'⟩ := mapM_some_mem h y hy
  exact sendTo_isM h'

theorem mapM_sendPeer_noM {s : RState} {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendPeer s q m) = some r) : NoM r := by
  intro y hy
  obtain ⟨a, _, h'⟩ := mapM_some_mem h y hy
  exact sendPeer_isM h'

theorem bcast_noM {s : RState} {m : Msg} {r : List Out} (h : bcast s m = some r) : NoM r :=
  mapM_sendPeer_noM h

theorem bcastPreAccept_noM {s : RState} {a b c : w32} {cs : List Cmd} {sq : w32} {d : Deps}
    {v : ValTag} {r : List Out} (h : bcastPreAccept s a b c cs sq d v = some r) : NoM r :=
  bcast_noM h
theorem bcastAccept_noM {s : RState} {a b c : w32} {cs : List Cmd} {sq : w32} {d : Deps}
    {v : ValTag} {r : List Out} (h : bcastAccept s a b c cs sq d v = some r) : NoM r :=
  bcast_noM h
theorem bcastCommit_noM {s : RState} {a b : w32} {cs : List Cmd} {sq : w32} {d : Deps}
    {v : ValTag} {r : List Out} (h : bcastCommit s a b cs sq d v = some r) : NoM r :=
  bcast_noM h
theorem bcastPrepare_noM {s : RState} {a b c : w32} {r : List Out}
    (h : bcastPrepare s a b c = some r) : NoM r :=
  bcast_noM h

theorem shortCircuit_noM {s s' : RState} {n : w32} {v : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n v f = some (s', o)) : NoM o := by
  obtain ⟨_, _, -, -, -, -, hsco⟩ := shortCircuit_spec h
  intro x hx
  obtain ⟨_, _, rfl, -⟩ := hsco x hx
  rfl

macro "nm_fin" : tactic => `(tactic| (first
  | exact noM_nil
  | exact noM_single rfl
  | with_reducible exact bcastPreAccept_noM ‹_›
  | with_reducible exact bcastAccept_noM ‹_›
  | with_reducible exact bcastCommit_noM ‹_›
  | with_reducible exact bcastPrepare_noM ‹_›
  | with_reducible exact noM_single (sendPeer_isM ‹sendPeer _ _ _ = some _›)
  | with_reducible exact noM_single (sendTo_isM ‹sendTo _ _ = some _›)
  | with_reducible exact mapM_sendTo_noM ‹_›
  | with_reducible exact mapM_sendPeer_noM ‹_›
  | exact noM_append (shortCircuit_noM ‹shortCircuit _ _ _ _ = some _›) (noM_single rfl)
  | exact noM_append noM_nil (noM_single rfl)
  | exact shortCircuit_noM ‹shortCircuit _ _ _ _ = some _›))

theorem startPhase1_noM {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o)) : NoM o := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; nm_fin)

theorem leaderCommit_noM {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit s q i c lb = .ok (s', o)) : NoM o := by
  unfold leaderCommit at h; peel h
  all_goals (cases h; nm_fin)

macro "nm_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; nm_fin; done)
    | exact leaderCommit_noM $h:ident
    | exact startPhase1_noM $h:ident)))

/-- The handlers that never output an RMW reply. -/
def Ev.mspecial : Ev → Bool
  | .msg (.executed _) => true
  | .msg (.executeOverwrite _) => true
  | _ => false

set_option maxHeartbeats 4000000 in
theorem step_noM {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) (he : Ev.mspecial e = false) : NoM o := by
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
    exact startPhase1_noM h
  | forceWrite => cases h; exact noM_nil
  | recover => change stepRecover _ _ _ = _ at h; unfold stepRecover at h; nm_close h
  | exec => change stepExec _ _ _ = _ at h; unfold stepExec at h; nm_close h
  | msg m =>
    cases m with
    | read1 => change stepRead1 _ _ = _ at h; unfold stepRead1 at h; nm_close h
    | read2 => change stepRead2 _ _ = _ at h; unfold stepRead2 at h; nm_close h
    | write1 => change stepWrite1 _ _ = _ at h; unfold stepWrite1 at h; nm_close h
    | write2 => change stepWrite2 _ _ = _ at h; unfold stepWrite2 at h; nm_close h
    | read1Reply => change stepRead1Reply _ _ = _ at h; unfold stepRead1Reply at h; nm_close h
    | read2Reply => change stepRead2Reply _ _ = _ at h; unfold stepRead2Reply at h; nm_close h
    | write1Reply => change stepWrite1Reply _ _ = _ at h; unfold stepWrite1Reply at h; nm_close h
    | write2Reply =>
      change stepWrite2Reply _ _ = _ at h; unfold stepWrite2Reply at h; peel h
      all_goals (cases h)
      all_goals (first
        | nm_fin
        | (rcases oite_some_iff.1 ‹(if _ then shortCircuit _ _ _ _ else some _) = some _› with
             ⟨-, hsc⟩ | ⟨-, hsc⟩
           · exact noM_append (shortCircuit_noM hsc) (noM_single rfl)
           · cases hsc; exact noM_append noM_nil (noM_single rfl)))
    | prepare => change stepPrepare _ _ = _ at h; unfold stepPrepare at h; nm_close h
    | preAccept => change stepPreAccept _ _ = _ at h; unfold stepPreAccept at h; nm_close h
    | accept => change stepAccept _ _ = _ at h; unfold stepAccept at h; nm_close h
    | commit => change stepCommit _ _ = _ at h; unfold stepCommit at h; nm_close h
    | prepareReply => change stepPrepareReply _ _ = _ at h; unfold stepPrepareReply at h; nm_close h
    | preAcceptReply =>
      change stepPreAcceptReply _ _ = _ at h; unfold stepPreAcceptReply at h; nm_close h
    | preAcceptOK => change stepPreAcceptOK _ _ = _ at h; unfold stepPreAcceptOK at h; nm_close h
    | acceptReply => change stepAcceptReply _ _ = _ at h; unfold stepAcceptReply at h; nm_close h
    | executed => cases he
    | executeOverwrite => cases he

/-! ## The steps' proposals -/

theorem step_pflow {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) :
    ∀ p, PropIn s' p → PropIn s p ∨ ∃ rid cid k d a b, e = .rmw rid cid k d a b ∧
      p.client = cid ∧ p.cmdId = rid := by
  have L : PFlow s s' → ∀ p, PropIn s' p → PropIn s p ∨ ∃ rid cid k d a b,
      e = .rmw rid cid k d a b ∧ p.client = cid ∧ p.cmdId = rid := fun hf p hp => Or.inl (hf p hp)
  cases e with
  | read => exact L (stepClientRead_eqip h).pf
  | write => exact L (stepClientWrite_eqip h).pf
  | rmw rid cid k d a b =>
    intro p hp
    rcases stepClientRMW_pf h p hp with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨rid, cid, k, d, a, b, rfl, h1, h2⟩
  | forceWrite => cases h; exact L (PFlow.rfl' _)
  | recover => exact L (stepRecover_pfl h)
  | exec => exact L (stepExec_pf h)
  | msg m =>
    cases m with
    | read1 => exact L (stepRead1_eqip h).pf
    | read2 => exact L (stepRead2_eqip h).pf
    | write1 => exact L (stepWrite1_eqip h).pf
    | write2 => exact L (stepWrite2_eqip h).pf
    | read1Reply => exact L (stepRead1Reply_eqip h).pf
    | read2Reply => exact L (stepRead2Reply_eqip h).pf
    | write1Reply => exact L (stepWrite1Reply_eqip h).pf
    | write2Reply => exact L (stepWrite2Reply_eqip h).pf
    | prepare => exact L (stepPrepare_pfl h)
    | preAccept => exact L (stepPreAccept_pf h)
    | accept => exact L (stepAccept_pf h)
    | commit => exact L (stepCommit_pf h)
    | prepareReply => exact L (stepPrepareReply_pfl h)
    | preAcceptReply => exact L (stepPreAcceptReply_pfl h)
    | preAcceptOK => exact L (stepPreAcceptOK_pfl h)
    | acceptReply => exact L (stepAcceptReply_pfl h)
    | executed => exact L (handleExecuted_pfl h)
    | executeOverwrite => exact L (stepExecuteOverwrite_pfl h)

/-! ## The ownership invariant -/

/-- Every proposal at `R` is owned by an RMW operation at `R` with its key. -/
def POwn (l : List Label) (c : Cfg gNet) : Prop :=
  ∀ R p, PropIn (stR c R) p → ∃ o ∈ ops l, o.r = R ∧ (∃ a b, o.inp = .cas a b) ∧
    o.cid = p.client ∧ o.rid = p.cmdId

theorem pown_init : POwn [] (Cfg.init gNet) := by
  intro R p hp
  change PropIn (RState.init R.val) p at hp
  rcases hp with hp | ⟨q, i, c, lb, hc, -⟩
  · cases hp
  · cases hc

theorem pown_step {l : List Label} {c c' : Cfg gNet} {i : Fin 3} {e : Ev} {x : List Ext}
    (h : GRun (Cfg.init gNet) l c) (hi : POwn l c) (hst : GStep c i e c' x) :
    POwn (l ++ [(i, e)]) c' := by
  obtain ⟨s', o, hs⟩ := StepAt.of h hst
  have hmono : ∀ o ∈ ops l, o ∈ ops (l ++ [(i, e)]) := fun o ho => by
    rw [ops_snoc]; exact List.mem_append_left _ ho
  intro R p hp
  by_cases hR : R = i
  · subst hR
    rw [hs.sti] at hp
    rcases step_pflow hs.ok p hp with h1 | ⟨rid, cid, k, d, a, b, rfl, h2, h3⟩
    · obtain ⟨o', ho', a1, a2, a3, a4⟩ := hi R p h1
      exact ⟨o', hmono o' ho', a1, a2, a3, a4⟩
    · rw [ops_snoc_req (l := l) (i := R) (e := .rmw rid cid k d a b) rfl]
      exact ⟨_, List.mem_append_right _ (List.mem_singleton.2 rfl), rfl, ⟨a, b, rfl⟩,
        h2.symm, h3.symm⟩
  · rw [hs.stj hR] at hp
    obtain ⟨o', ho', a1, a2, a3, a4⟩ := hi R p hp
    exact ⟨o', hmono o' ho', a1, a2, a3, a4⟩

/-- **Every proposal is owned by an RMW.** -/
theorem pown {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) : POwn l c :=
  grun_inv POwn pown_init (fun _ _ _ _ _ _ h hi hs => pown_step h hi hs) l c h

/-! ## RMW replies -/

theorem handleExecuted_rmw {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) {cid rid : w32} {f : w8}
    (hx : Out.ext (.rmwReply cid rid f) ∈ o) : ∃ p, PropIn s p ∧ p.client = cid ∧ p.cmdId = rid := by
  unfold handleExecuted at h; peel h
  all_goals (cases h)
  all_goals (first | (simp at hx; done) | skip)
  -- (independent of the `c.cmds.head?` guard, which G43's fix removes)
  simp only [List.mem_singleton, Out.ext.injEq, Ext.rmwReply.injEq] at hx
  obtain ⟨rfl, rfl, -⟩ := hx
  exact ⟨_, Or.inr ⟨_, _, _, _, ‹s.inst _ _ = some _›, ‹Copy.lb _ = some _›,
    List.mem_of_head? ‹(_ : List Proposal).head? = some _›⟩, rfl, rfl⟩

/-- An RMW reply is output by `handleExecuted` (directly, or after an `ExecuteOverwrite`), from a
proposal of the state. -/
theorem rmwReply_prop {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) {cid rid : w32} {f : w8}
    (hx : Out.ext (.rmwReply cid rid f) ∈ o) : ∃ p, PropIn s p ∧ p.client = cid ∧ p.cmdId = rid := by
  cases hm : Ev.mspecial e with
  | false => exact absurd (step_noM h hm _ hx) (by simp [isMOut])
  | true =>
    cases e with
    | msg m =>
      cases m with
      | executed m => exact handleExecuted_rmw h hx
      | executeOverwrite m =>
        change stepExecuteOverwrite _ _ = _ at h
        unfold stepExecuteOverwrite at h; peel h
        · obtain ⟨p, hp, a, b⟩ := handleExecuted_rmw h hx
          exact ⟨p, pflow_overwrite (PFlow.rfl' s) _ _ p hp, a, b⟩
        all_goals (cases h; simp [isMOut] at hx
                   have := sendPeer_isM ‹sendPeer _ _ _ = some _›
                   rw [← hx] at this; cases this)
      | _ => cases hm
    | _ => cases hm

end Perennial.gryff.pure
