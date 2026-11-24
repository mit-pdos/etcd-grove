/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/AEStep.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AE, internal: replica-local facts every step keeps, for the execution chain (`exec_agree`).
* `Ids s`: a copy at `(q, i)` has `leader = q`, `slot = i` (the executor's sort key uses them).
* `IStep s t` (every step but `exec`): `Ids` is kept, `prevValTag` is unchanged, and no copy
  becomes EXECUTED (only `stepExec` sets EXECUTED or `prevValTag`).
* `stepExec_shape`: what an execution does.
Per handler by unit L's `peel`, in the style of unit A1's `PureA/Exec.lean`.
-/
module

public import Dsverify.Proof.gryff.PureA.Exec

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AE

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.pureA

/-- Copies carry their own instance's coordinates. -/
def Ids (s : RState) : Prop := ∀ q i cp, s.inst q i = some cp → cp.leader = q ∧ cp.slot = i

/-- No copy becomes EXECUTED. -/
def NoNewEx (s t : RState) : Prop :=
  ∀ q i cp, t.inst q i = some cp → cp.status = St.EXECUTED →
    ∃ cp0, s.inst q i = some cp0 ∧ cp0.status = St.EXECUTED

/-- A step other than an execution. -/
def IStep (s t : RState) : Prop := (Ids s → Ids t) ∧ t.prevValTag = s.prevValTag ∧ NoNewEx s t

theorem istep_refl (s : RState) : IStep s s := ⟨id, rfl, fun _ _ cp h e => ⟨cp, h, e⟩⟩

theorem istep_trans {a b c : RState} (h1 : IStep a b) (h2 : IStep b c) : IStep a c := by
  refine ⟨fun h => h2.1 (h1.1 h), h2.2.1.trans h1.2.1, fun q i cp h e => ?_⟩
  obtain ⟨cp1, h3, h4⟩ := h2.2.2 q i cp h e
  exact h1.2.2 q i cp1 h3 h4

theorem istep_frame {s t u : RState} (h : IStep s t) (e1 : u.inst = t.inst)
    (e2 : u.prevValTag = t.prevValTag) : IStep s u := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun hI q i cp hc => h1 hI q i cp (e1 ▸ hc), e2.trans h2, fun q i cp hc => h3 q i cp (e1 ▸ hc)⟩

theorem istep_setInst {s t : RState} {q i : w32} {c : Copy} (h : IStep s t)
    (hc : Ids s → c.leader = q ∧ c.slot = i)
    (hx : c.status = St.EXECUTED → ∃ cp0, s.inst q i = some cp0 ∧ cp0.status = St.EXECUTED) :
    IStep s (t.setInst q i c) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun hI q' i' cp hq => ?_, h2, fun q' i' cp hq e => ?_⟩
  · rw [setInst_inst] at hq
    split at hq
    · rename_i hh; obtain ⟨rfl, rfl⟩ := hh; cases hq; exact hc hI
    · exact h1 hI q' i' cp hq
  · rw [setInst_inst] at hq
    split at hq
    · rename_i hh; obtain ⟨rfl, rfl⟩ := hh; cases hq; exact hx e
    · exact h3 q' i' cp hq e

theorem updateConflicts_pvt (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).prevValTag = s.prevValTag := by
  unfold updateConflicts
  apply forIn_id_invA (P := fun x : RState => x.prevValTag = s.prevValTag) _ _ _ rfl
  intro a b hb
  simpa using hb

theorem updateCommitted_pvt {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    s'.prevValTag = s.prevValTag := by
  unfold updateCommitted at h; opeel h
  all_goals (cases h; rfl)

theorem istep_updConf {s t : RState} (h : IStep s t) (cmds : List Cmd) (q i sq : w32) :
    IStep s (updateConflicts t cmds q i sq) :=
  istep_frame h (updateConflicts_inst _ _ _ _ _).1 (updateConflicts_pvt _ _ _ _ _)
theorem istep_updCommitted {s t t' : RState} {q : w32} (h : IStep s t)
    (hu : updateCommitted t q = some t') : IStep s t' :=
  istep_frame h (updateCommitted_inst hu).1 (updateCommitted_pvt hu)
theorem istep_proposeQ {s t : RState} (h : IStep s t) (x : List Proposal) :
    IStep s { t with proposeQ := x } := h
theorem istep_setCrt {s t : RState} (h : IStep s t) (q x : w32) : IStep s (t.setCrt q x) := h

/-- The side condition for a copy built from an old one. -/
theorem idsc {s : RState} {q i : w32} {c c' : Copy} (hc : s.inst q i = some c)
    (e1 : c'.leader = c.leader) (e2 : c'.slot = c.slot) : Ids s → c'.leader = q ∧ c'.slot = i := by
  intro hI; obtain ⟨h1, h2⟩ := hI q i c hc; exact ⟨e1.trans h1, e2.trans h2⟩

theorem exc {s : RState} {q i : w32} {c c' : Copy} (hc : s.inst q i = some c)
    (e : c'.status = c.status) :
    c'.status = St.EXECUTED → ∃ cp0, s.inst q i = some cp0 ∧ cp0.status = St.EXECUTED :=
  fun h => ⟨c, hc, e ▸ h⟩

theorem exc_ne {s : RState} {q i : w32} {c' : Copy} {a : w8} (e : c'.status = a)
    (ha : a ≠ St.EXECUTED) :
    c'.status = St.EXECUTED → ∃ cp0, s.inst q i = some cp0 ∧ cp0.status = St.EXECUTED :=
  fun h => absurd (e.symm.trans h) ha

macro "asm" : term => `((by with_reducible assumption))

macro "iside1" : tactic => `(tactic| (first
    | (exact fun _ => ⟨rfl, rfl⟩)
    | (intro hI; try dsimp only
       apply hI; assumption; done)))

macro "iside" : tactic => `(tactic| (first
    | iside1
    | (split <;> iside1; done)))

macro "xside1" : tactic => `(tactic| (first
    | (intro hx; dsimp only at hx; exact absurd hx (by decide); done)
    | (intro hx; dsimp only at hx; split at hx <;> exact absurd hx (by decide); done)
    | (intro hx; try dsimp only at hx
       exact ⟨_, by assumption, hx⟩; done)))

macro "xside" : tactic => `(tactic| (first
    | xside1
    | (split <;> xside1; done)))

macro "istep_fin" : tactic => `(tactic| (
  repeat (first
    | exact istep_refl _
    | (apply istep_updCommitted ?_ ‹updateCommitted _ _ = some _›)
    | apply istep_updConf
    | apply istep_setInst
    | apply istep_proposeQ
    | apply istep_setCrt)
  all_goals (first | iside | xside)))

set_option maxRecDepth 20000

theorem leaderCommit_istep {s t t' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit t q i c lb = .ok (t', o)) (ht : IStep s t)
    (hc : Ids s → c.leader = q ∧ c.slot = i) : IStep s t' := by
  unfold leaderCommit at h; peel h
  · cases h
    obtain hU := ‹updateCommitted _ _ = some _›
    refine istep_setInst (istep_proposeQ (istep_updCommitted (istep_setInst ht ?_ ?_) hU) _) ?_ ?_
    · exact hc
    · xside
    · exact hc
    · xside
  · cases h
    refine istep_updCommitted (istep_setInst ht ?_ ?_) ‹updateCommitted _ _ = some _›
    · exact hc
    · xside

theorem startPhase1_istep {s t t' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 t q i b ps cs = .ok (t', o)) (ht : IStep s t) :
    IStep s t' := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; apply istep_updConf; apply istep_setInst ht; exact fun _ => ⟨rfl, rfl⟩; xside)

macro "istep_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; istep_fin; done)
    | (refine leaderCommit_istep $h:ident ?_ ?_ <;> istep_fin; done)
    | (refine startPhase1_istep $h:ident ?_; istep_fin; done))))

theorem stepPreAccept_istep {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) : IStep s s' := by
  unfold stepPreAccept at h; peel h
  all_goals (cases h; istep_fin)
theorem stepAccept_istep {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) : IStep s s' := by
  unfold stepAccept at h; istep_close h
theorem stepCommit_istep {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) : IStep s s' := by
  unfold stepCommit at h; istep_close h
theorem stepPreAcceptReply_istep {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) : IStep s s' := by
  unfold stepPreAcceptReply at h; istep_close h
theorem stepPreAcceptOK_istep {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) : IStep s s' := by
  unfold stepPreAcceptOK at h; istep_close h
theorem stepAcceptReply_istep {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) : IStep s s' := by
  unfold stepAcceptReply at h; istep_close h
theorem stepPrepare_istep {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) : IStep s s' := by
  unfold stepPrepare at h; istep_close h
theorem stepPrepareReply_istep {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) : IStep s s' := by
  unfold stepPrepareReply at h; istep_close h
theorem handleExecuted_istep {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) : IStep s s' := by
  unfold handleExecuted at h; istep_close h
theorem stepRecover_istep {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) : IStep s s' := by
  unfold stepRecover at h; istep_close h

end Perennial.gryff.pureA.AE

namespace Perennial.gryff.pureA.AE

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.pureA

/-! ## The Gryff handlers: instance space and `prevValTag` untouched -/

def PF (s t : RState) : Prop := t.inst = s.inst ∧ t.prevValTag = s.prevValTag

theorem pf_istep {s t : RState} (h : PF s t) : IStep s t :=
  istep_frame (istep_refl s) h.1 h.2

theorem overwrite_pf (s : RState) (v : w64) (t : model.Tag) : PF s (s.overwrite v t) := by
  unfold RState.overwrite; split <;> exact ⟨rfl, rfl⟩

theorem ow_pvt (s : RState) (v : w64) (t : model.Tag) :
    (s.overwrite v t).prevValTag = s.prevValTag := (overwrite_pf s v t).2

theorem shortCircuit_pf {s s' : RState} {n : w32} {v : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n v f = some (s', o)) : PF s s' := by
  unfold shortCircuit at h
  opeel h
  all_goals
    cases h
    refine forIn_opt_invA _ _ _ (fun p : RState × List Out => PF s p.1) ⟨rfl, rfl⟩ ?_ _ ‹_›
    intro a b st hb hf
    opeel hf
    all_goals (cases hf; exact hb)

theorem shortCircuit_ite_pf {s s' : RState} {c : Prop} [Decidable c] {n : w32} {v : ValTag}
    {f : Bool} {o : List Out}
    (h : (if c then shortCircuit s n v f else some (s, [])) = some (s', o)) : PF s s' := by
  split at h
  · exact shortCircuit_pf h
  · cases h; exact ⟨rfl, rfl⟩

macro "pf_fin" : tactic => `(tactic| (
  try (have hsc := shortCircuit_pf ‹shortCircuit _ _ _ _ = some _›
       obtain ⟨hs1, hs2⟩ := hsc)
  try (have hsc := shortCircuit_ite_pf ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›
       obtain ⟨hs1, hs2⟩ := hsc)
  refine ⟨?_, ?_⟩ <;> simp only [ow_inst, ow_pvt] <;>
    first | rfl | assumption))

macro "pf_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (cases $h:ident; pf_fin)))

theorem stepRead1_pf {s s' : RState} {m : Read1ProxiedM} {o : List Out}
    (h : stepRead1 s m = .ok (s', o)) : PF s s' := by
  unfold stepRead1 at h; pf_close h
theorem stepRead2_pf {s s' : RState} {m : Read2ProxiedM} {o : List Out}
    (h : stepRead2 s m = .ok (s', o)) : PF s s' := by
  unfold stepRead2 at h; pf_close h
theorem stepWrite1_pf {s s' : RState} {m : Write1ProxiedM} {o : List Out}
    (h : stepWrite1 s m = .ok (s', o)) : PF s s' := by
  unfold stepWrite1 at h; pf_close h
theorem stepWrite2_pf {s s' : RState} {m : Write2ProxiedM} {o : List Out}
    (h : stepWrite2 s m = .ok (s', o)) : PF s s' := by
  unfold stepWrite2 at h; pf_close h
theorem stepRead1Reply_pf {s s' : RState} {m : Read1ReplyM} {o : List Out}
    (h : stepRead1Reply s m = .ok (s', o)) : PF s s' := by
  unfold stepRead1Reply at h; pf_close h
theorem stepRead2Reply_pf {s s' : RState} {m : Read2ReplyM} {o : List Out}
    (h : stepRead2Reply s m = .ok (s', o)) : PF s s' := by
  unfold stepRead2Reply at h; pf_close h
theorem stepWrite1Reply_pf {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) : PF s s' := by
  unfold stepWrite1Reply at h; pf_close h
theorem stepWrite2Reply_pf {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (h : stepWrite2Reply s m = .ok (s', o)) : PF s s' := by
  unfold stepWrite2Reply at h; pf_close h
theorem stepClientWrite_pf {s s' : RState} {rid cid : w32} {k v : w64} {d : Dep} {o : List Out}
    (h : stepClientWrite s rid cid k v d = .ok (s', o)) : PF s s' := by
  unfold stepClientWrite at h; pf_close h
theorem stepClientRead_pf {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {o : List Out}
    (h : stepClientRead s rid cid k d = .ok (s', o)) : PF s s' := by
  unfold stepClientRead at h
  peel h
  cases h
  have hx := ‹forIn _ _ _ = Except.ok s'›
  refine forIn_exc_invA _ _ _ (fun x : RState => PF s x) ?_ ?_ _ hx
  · exact ⟨rfl, rfl⟩
  intro a b st hb hf
  peel hf
  all_goals (cases hf; exact hb)

set_option maxRecDepth 20000

theorem handlePropose_istep {s s' : RState} {p : Proposal} {o : List Out}
    (h : handlePropose s p = .ok (s', o)) : IStep s s' := by
  obtain ⟨-, -, h⟩ := handlePropose_ok h; unfold handleProposeBody at h; peel h
  all_goals exact startPhase1_istep h (istep_proposeQ (istep_setCrt (istep_refl _) _ _) _)

theorem stepClientRMW_istep {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    {o : List Out} (h : stepClientRMW s rid cid k d a b = .ok (s', o)) : IStep s s' := by
  unfold stepClientRMW at h; peel h
  have h2 := handlePropose_istep h
  exact ⟨fun hI => h2.1 hI, h2.2.1, h2.2.2⟩

theorem stepExecuteOverwrite_istep {s s' : RState} {m : ExecuteOverwriteM} {o : List Out}
    (h : stepExecuteOverwrite s m = .ok (s', o)) : IStep s s' := by
  have hs : IStep s (s.overwrite m.v m.t) := pf_istep (overwrite_pf s m.v m.t)
  unfold stepExecuteOverwrite at h; peel h
  · exact istep_trans hs (handleExecuted_istep h)
  · cases h; exact hs

/-- **Every step but an execution** keeps `Ids`, `prevValTag`, and makes nothing EXECUTED. -/
theorem step_istep {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) (he : ∀ q i, e ≠ .exec q i) : IStep s s' := by
  cases e with
  | read => exact pf_istep (stepClientRead_pf h)
  | write => exact pf_istep (stepClientWrite_pf h)
  | rmw => exact stepClientRMW_istep h
  | forceWrite => cases h; exact istep_refl _
  | recover => exact stepRecover_istep h
  | exec q i => exact absurd rfl (he q i)
  | msg m =>
    cases m with
    | read1 => exact pf_istep (stepRead1_pf h)
    | read2 => exact pf_istep (stepRead2_pf h)
    | write1 => exact pf_istep (stepWrite1_pf h)
    | write2 => exact pf_istep (stepWrite2_pf h)
    | read1Reply => exact pf_istep (stepRead1Reply_pf h)
    | read2Reply => exact pf_istep (stepRead2Reply_pf h)
    | write1Reply => exact pf_istep (stepWrite1Reply_pf h)
    | write2Reply => exact pf_istep (stepWrite2Reply_pf h)
    | prepare => exact stepPrepare_istep h
    | preAccept => exact stepPreAccept_istep h
    | accept => exact stepAccept_istep h
    | commit => exact stepCommit_istep h
    | prepareReply => exact stepPrepareReply_istep h
    | preAcceptReply => exact stepPreAcceptReply_istep h
    | preAcceptOK => exact stepPreAcceptOK_istep h
    | acceptReply => exact stepAcceptReply_istep h
    | executed => exact handleExecuted_istep h
    | executeOverwrite => exact stepExecuteOverwrite_istep h

end Perennial.gryff.pureA.AE

namespace Perennial.gryff.pureA.AE

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.pureA

/-! ## An execution -/

/-- The result of executing a copy with base `base` and first command `c0` after the previous
result `prev` (`stepExec`). -/
def resNext (prev : Option ValTag) (base : ValTag) (c0 : Cmd) : ValTag :=
  let vt0 : ValTag := match prev with
    | none => base
    | some pvt => if base.t.gt pvt.t then base else pvt
  let vt1 : ValTag := if c0.oldV = vt0.v then { vt0 with v := c0.v } else vt0
  { vt1 with t := { vt1.t with rmwc := vt1.t.rmwc + 1 } }

theorem execRes_nil : execRes [] = none := rfl

set_option maxRecDepth 20000 in
theorem stepExec_shape {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) :
    ∃ c, inBox q i = true ∧ s.inst q i = some c ∧ c.status = St.COMMITTED ∧
      execGuard s (sint.Z q, sint.Z i) ∧
      s'.inst = (s.setInst q i { c with status := St.EXECUTED }).inst ∧
      ((c.cmds = [] ∧ execRes o = none ∧ s'.prevValTag = s.prevValTag) ∨
       (∃ c0 rest, c.cmds = c0 :: rest ∧ execRes o = some (resNext s.prevValTag c.base c0) ∧
          s'.prevValTag = some (resNext s.prevValTag c.base c0))) := by
  unfold stepExec at h; peel h
  all_goals (
    cases h
    refine ⟨_, by simpa using ‹¬ (!inBox q i) = true›, ‹_›, by simpa using ‹¬ _ ≠ St.COMMITTED›,
      by simpa using ‹¬¬ execGuard _ _›, rfl, ?_⟩
    first
    | exact Or.inl ⟨‹_›, rfl, rfl⟩
    | (refine Or.inr ⟨_, _, ‹_›, ?_, ?_⟩
       all_goals (
         try (obtain ⟨d, -, hd⟩ := Option.map_eq_some_iff.1 ‹sendTo _ _ = some _›; subst hd)
         first
         | rfl
         | (simp only [resNext, execRes, List.findSome?_cons, List.findSome?_nil,
              RState.setInst] at *; simp_all))))

end Perennial.gryff.pureA.AE
