/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/Exec.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1, internal: **a replica executes an instance at most once** (`exec_twice`, behind
`exec_nodup`). Replica-local: no agreement needed.
* `Frame`: the Gryff handlers leave the instance space, `crtInstance` and the id alone.
* `ExecKeep s s'`: an EXECUTED copy stays EXECUTED (every handler checks the status before
  overwriting a copy; the exception, `handlePropose`'s `startPhase1` at `(id, crt[id])`, needs `Loc`).
* `Loc s`: copies of the own row at or above `crt[id]` are bare NONE copies (only `stepPrepare`
  creates copies without raising `crt`; every other creation of an own-row copy raises `crt` past it
  or is guarded by `i < crt`); `LStep s s'` is a step's effect on the own row, giving `Loc s'`.
* `step_lk`: every step (per handler, by unit L's `peel`), `runP_loc`, `runP_keep`, `exec_twice`.
-/
module

public import Dsverify.Proof.gryff.PureL.Peel
public import Dsverify.Proof.gryff.PureL.Run
public import Dsverify.Proof.gryff.PureA.Concrete

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA

open Perennial Perennial.gryff.model Perennial.gryff.pure

/-! Loop invariants (copied from unit L's `PureL/StoreSteps.lean`, which `Pure/Agree.lean` cannot
import). -/

theorem forIn_id_invA {α β : Type} (l : List α) (b : β) (f : α → β → Id (ForInStep β))
    (P : β → Prop) (h0 : P b) (hf : ∀ a b, P b → P (f a b).run.value) : P (forIn l b f).run := by
  induction l generalizing b with
  | nil => exact h0
  | cons a l ih =>
    rw [List.forIn_cons]
    have := hf a b h0
    cases hfa : f a b with
    | done b' => rw [hfa] at this; exact this
    | yield b' => rw [hfa] at this; exact ih b' this

theorem forIn_opt_invA {α β : Type} (l : List α) (b : β) (f : α → β → Option (ForInStep β))
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

theorem forIn_exc_invA {ε α β : Type} (l : List α) (b : β) (f : α → β → Except ε (ForInStep β))
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

/-- An EXECUTED copy stays EXECUTED. -/
def ExecKeep (s s' : RState) : Prop :=
  ∀ q i cp, s.inst q i = some cp → cp.status = St.EXECUTED →
    ∃ cp', s'.inst q i = some cp' ∧ cp'.status = St.EXECUTED

theorem setInst_inst (s : RState) (q i : w32) (c : Copy) (q' i' : w32) :
    (s.setInst q i c).inst q' i' = if q' = q ∧ i' = i then some c else s.inst q' i' := rfl

theorem updateCommitted_inst {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    s'.inst = s.inst ∧ s'.id = s.id ∧ s'.crtInstance = s.crtInstance := by
  unfold updateCommitted at h; opeel h
  all_goals (cases h; exact ⟨rfl, rfl, rfl⟩)

theorem updateConflicts_inst (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).inst = s.inst ∧ (updateConflicts s cmds q i sq).id = s.id ∧
      (updateConflicts s cmds q i sq).crtInstance = s.crtInstance := by
  unfold updateConflicts
  apply forIn_id_invA (P := fun x : RState => x.inst = s.inst ∧ x.id = s.id ∧
    x.crtInstance = s.crtInstance) _ _ _ ⟨rfl, rfl, rfl⟩
  intro a b hb
  simpa using hb

theorem stepCommit_keep {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) : ExecKeep s s' := by
  unfold stepCommit at h; peel h
  all_goals (
    cases h
    intro q i cp hcp hex
    repeat (first
      | (rename_i hU; obtain ⟨hu1, -, -⟩ := updateCommitted_inst hU; rw [hu1]; clear hU)
      | fail)
    try simp only [setInst_inst, RState.setCrt, (updateConflicts_inst _ _ _ _ _).1] at *
    try (split <;> rename_i hqi)
    all_goals (first | exact ⟨cp, hcp, hex⟩ | (obtain ⟨rfl, rfl⟩ := hqi; simp_all) | simp_all))


/-! ## Steps that leave the instance space alone (the Gryff handlers) -/


/-- A step that does not touch the instance space, the `crtInstance` row nor the id. -/
def Frame (s t : RState) : Prop := t.id = s.id ∧ t.inst = s.inst ∧ t.crtInstance = s.crtInstance

theorem Frame.trans' {a b c : RState} (h1 : Frame a b) (h2 : Frame b c) : Frame a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem overwrite_frame (s : RState) (v : w64) (t : model.Tag) : Frame s (s.overwrite v t) := by
  unfold RState.overwrite; split <;> exact ⟨rfl, rfl, rfl⟩

theorem shortCircuit_frame {s s' : RState} {n : w32} {v : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n v f = some (s', o)) : Frame s s' := by
  rcases Perennial.gryff.model.shortCircuit_cases h with h | ⟨rfl, rfl⟩
  rotate_left
  · exact ⟨rfl, rfl, rfl⟩
  unfold Perennial.gryff.model.shortCircuitReads at h
  opeel h
  all_goals
    cases h
    refine forIn_opt_invA _ _ _ (fun p : RState × List Out => Frame s p.1) ⟨rfl, rfl, rfl⟩ ?_ _ ‹_›
    intro a b st hb hf
    opeel hf
    all_goals (cases hf; exact hb)

theorem shortCircuit_ite_frame {s s' : RState} {c : Prop} [Decidable c] {n : w32} {v : ValTag}
    {f : Bool} {o : List Out}
    (h : (if c then shortCircuit s n v f else some (s, [])) = some (s', o)) : Frame s s' := by
  split at h
  · exact shortCircuit_frame h
  · cases h; exact ⟨rfl, rfl, rfl⟩

theorem ow_id (s : RState) (v : w64) (t : model.Tag) : (s.overwrite v t).id = s.id := (overwrite_frame s v t).1
theorem ow_inst (s : RState) (v : w64) (t : model.Tag) : (s.overwrite v t).inst = s.inst := (overwrite_frame s v t).2.1
theorem ow_crt (s : RState) (v : w64) (t : model.Tag) : (s.overwrite v t).crtInstance = s.crtInstance :=
  (overwrite_frame s v t).2.2

macro "frame_fin" : tactic => `(tactic| (
  try (have hsc := shortCircuit_frame ‹shortCircuit _ _ _ _ = some _›
       obtain ⟨hs1, hs2, hs3⟩ := hsc)
  try (have hsc := shortCircuit_ite_frame ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›
       obtain ⟨hs1, hs2, hs3⟩ := hsc)
  refine ⟨?_, ?_, ?_⟩ <;> simp only [ow_id, ow_inst, ow_crt] <;>
    first | rfl | assumption))

macro "frame_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (cases $h:ident; frame_fin)))

theorem stepRead1_frame {s s' : RState} {m : Read1ProxiedM} {o : List Out}
    (h : stepRead1 s m = .ok (s', o)) : Frame s s' := by
  unfold stepRead1 at h; frame_close h
theorem stepRead2_frame {s s' : RState} {m : Read2ProxiedM} {o : List Out}
    (h : stepRead2 s m = .ok (s', o)) : Frame s s' := by
  unfold stepRead2 at h; frame_close h
theorem stepWrite1_frame {s s' : RState} {m : Write1ProxiedM} {o : List Out}
    (h : stepWrite1 s m = .ok (s', o)) : Frame s s' := by
  unfold stepWrite1 at h; frame_close h
theorem stepWrite2_frame {s s' : RState} {m : Write2ProxiedM} {o : List Out}
    (h : stepWrite2 s m = .ok (s', o)) : Frame s s' := by
  unfold stepWrite2 at h; frame_close h
theorem stepRead1Reply_frame {s s' : RState} {m : Read1ReplyM} {o : List Out}
    (h : stepRead1Reply s m = .ok (s', o)) : Frame s s' := by
  unfold stepRead1Reply at h; frame_close h
theorem stepRead2Reply_frame {s s' : RState} {m : Read2ReplyM} {o : List Out}
    (h : stepRead2Reply s m = .ok (s', o)) : Frame s s' := by
  unfold stepRead2Reply at h; frame_close h
theorem stepWrite1Reply_frame {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) : Frame s s' := by
  unfold stepWrite1Reply at h; frame_close h
theorem stepWrite2Reply_frame {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (h : stepWrite2Reply s m = .ok (s', o)) : Frame s s' := by
  unfold stepWrite2Reply at h; frame_close h
theorem stepClientWrite_frame {s s' : RState} {rid cid : w32} {k v : w64} {d : Dep} {o : List Out}
    (h : stepClientWrite s rid cid k v d = .ok (s', o)) : Frame s s' := by
  unfold stepClientWrite at h; frame_close h
theorem stepClientRead_frame {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {o : List Out}
    (h : stepClientRead s rid cid k d = .ok (s', o)) : Frame s s' := by
  unfold stepClientRead at h
  peel h
  cases h
  have hx := ‹forIn _ _ _ = Except.ok s'›
  refine forIn_exc_invA _ _ _ (fun x : RState => Frame s x) ?_ ?_ _ hx
  · exact ⟨rfl, rfl, rfl⟩
  intro a b st hb hf
  peel hf
  all_goals (cases hf; exact hb)

/-! ## EXECUTED stays EXECUTED -/


theorem setCrt_inst' (s : RState) (q x : w32) : (s.setCrt q x).inst = s.inst := rfl

theorem keep_refl (s : RState) : ExecKeep s s := fun _ _ cp h e => ⟨cp, h, e⟩
theorem keep_inst {s t t' : RState} (h : ExecKeep s t) (e : t'.inst = t.inst) : ExecKeep s t' := by
  intro q i cp h1 h2; rw [e]; exact h q i cp h1 h2
theorem keep_trans {a b c : RState} (h1 : ExecKeep a b) (h2 : ExecKeep b c) : ExecKeep a c := by
  intro q i cp h e
  obtain ⟨cp1, h3, h4⟩ := h1 q i cp h e
  exact h2 q i cp1 h3 h4
theorem keep_setInst {s t : RState} {q i : w32} {c : Copy} (h : ExecKeep s t)
    (hc : ∀ c0, t.inst q i = some c0 → c0.status = St.EXECUTED → c.status = St.EXECUTED) :
    ExecKeep s (t.setInst q i c) := by
  intro q' i' cp h1 h2
  obtain ⟨cp1, h3, h4⟩ := h q' i' cp h1 h2
  rw [setInst_inst]
  by_cases e : q' = q ∧ i' = i
  · rw [if_pos e]; obtain ⟨rfl, rfl⟩ := e; exact ⟨c, rfl, hc cp1 h3 h4⟩
  · rw [if_neg e]; exact ⟨cp1, h3, h4⟩
theorem keep_updConf {s t : RState} (h : ExecKeep s t) (cmds : List Cmd) (q i sq : w32) :
    ExecKeep s (updateConflicts t cmds q i sq) := keep_inst h (updateConflicts_inst _ _ _ _ _).1
theorem keep_updCommitted {s t t' : RState} {q : w32} (h : ExecKeep s t)
    (hu : updateCommitted t q = some t') : ExecKeep s t' := keep_inst h (updateCommitted_inst hu).1
theorem keep_proposeQ {s t : RState} (h : ExecKeep s t) (x : List Proposal) :
    ExecKeep s { t with proposeQ := x } := h
theorem keep_prevValTag {s t : RState} (h : ExecKeep s t) (x : Option ValTag) :
    ExecKeep s { t with prevValTag := x } := h
theorem keep_setCrt {s t : RState} (h : ExecKeep s t) (q x : w32) :
    ExecKeep s (t.setCrt q x) := h

theorem st_contra {x a : w8} (h1 : x = St.EXECUTED) (h2 : ¬ x ≠ a) (ha : a ≠ St.EXECUTED) : False :=
  ha (h1 ▸ Classical.not_not.mp h2).symm

macro "keep_fin" : tactic => `(tactic| (
  repeat (first
    | exact keep_refl _
    | (apply keep_updCommitted ?_ ‹updateCommitted _ _ = some _›)
    | apply keep_updConf
    | apply keep_setInst
    | apply keep_proposeQ
    | apply keep_prevValTag
    | exact keep_setCrt (keep_refl _) _ _)
  all_goals (
    intro c0 hc0 hex
    try simp only [setCrt_inst', setInst_inst, (updateConflicts_inst _ _ _ _ _).1] at hc0
    first
      | exact hex
      | exact absurd hex (‹∀ c, RState.inst _ _ _ = some c → _ ≠ St.EXECUTED› _ hc0)
      | rfl
      | (split <;> exact hex)
      | (simp only [eq_self_iff_true, and_self, ↓reduceIte, Option.some.injEq] at hc0
         subst hc0
         first
           | exact absurd (Or.inr (Or.inr hex)) ‹_›
           | exact absurd (Or.inr hex) ‹_›
           | exact (st_contra hex ‹_› (by decide)).elim)
      | (simp only [hc0, Option.some.injEq] at *; subst_vars
         first
           | exact hex
           | exact absurd hex (‹∀ c, _ = c → _› _ rfl)
           | exact (‹∀ c, _ = c → False› _ rfl).elim
           | (cases ‹some _ = none›)
           | exact absurd (Or.inr (Or.inr hex)) ‹_›
           | exact absurd (Or.inr hex) ‹_›
           | exact (st_contra hex ‹_› (by decide)).elim
           | (split <;> exact hex)
           | fail))))

set_option maxRecDepth 20000

theorem leaderCommit_keep {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit s q i c lb = .ok (s', o))
    (hn : ∀ c0, s.inst q i = some c0 → c0.status ≠ St.EXECUTED) : ExecKeep s s' := by
  unfold leaderCommit at h; peel h
  · cases h
    obtain hU := ‹updateCommitted _ _ = some _›
    refine keep_setInst (keep_proposeQ (keep_updCommitted (keep_setInst (keep_refl _) ?_) hU) _) ?_
    · intro c0 hc0 hex; exact absurd hex (hn _ hc0)
    · intro c0 hc0 hex
      rw [(updateCommitted_inst hU).1, setInst_inst] at hc0
      simp only [eq_self_iff_true, and_self, ↓reduceIte, Option.some.injEq] at hc0
      subst hc0; exact hex
  · cases h
    obtain hU := ‹updateCommitted _ _ = some _›
    refine keep_updCommitted (keep_setInst (keep_refl _) ?_) hU
    intro c0 hc0 hex; exact absurd hex (hn _ hc0)

theorem startPhase1_keep {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o))
    (hn : ∀ c0, s.inst q i = some c0 → c0.status ≠ St.EXECUTED) : ExecKeep s s' := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; keep_fin)
  all_goals (exact absurd ‹_ = St.EXECUTED› (hn _ ‹_›))

macro "keep_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; keep_fin; done)
    | (refine keep_trans ?_ (leaderCommit_keep $h:ident ?_); keep_fin
       done)
    | (refine keep_trans ?_ (startPhase1_keep $h:ident ?_); keep_fin
       done))))

set_option maxRecDepth 20000 in
theorem stepPreAccept_keep {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) : ExecKeep s s' := by
  unfold stepPreAccept at h; keep_close h
theorem stepAccept_keep {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) : ExecKeep s s' := by
  unfold stepAccept at h; keep_close h
theorem stepPreAcceptReply_keep {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) : ExecKeep s s' := by
  unfold stepPreAcceptReply at h; keep_close h
theorem stepPreAcceptOK_keep {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) : ExecKeep s s' := by
  unfold stepPreAcceptOK at h; keep_close h
theorem stepAcceptReply_keep {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) : ExecKeep s s' := by
  unfold stepAcceptReply at h; keep_close h
theorem stepPrepare_keep {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) : ExecKeep s s' := by
  unfold stepPrepare at h; keep_close h
theorem stepPrepareReply_keep {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) : ExecKeep s s' := by
  unfold stepPrepareReply at h; keep_close h
theorem handleExecuted_keep {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) : ExecKeep s s' := by
  unfold handleExecuted at h; keep_close h
theorem stepRecover_keep {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) : ExecKeep s s' := by
  unfold stepRecover at h; keep_close h
theorem stepExec_keep {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) : ExecKeep s s' := by
  unfold stepExec at h; keep_close h

/-! ## The own row's shape (`Loc`) -/


/-- The own row's shape: copies at or above `crt[id]` are bare NONE copies. -/
def Loc (s : RState) : Prop :=
  s.id.toNat < 3 ∧ s.crtInstance.length = 3 ∧
  ∀ j cp, s.inst s.id j = some cp → sint.Z (s.crt s.id) ≤ sint.Z j → cp.status = St.NONE ∧ cp.lb = none

/-- A step's effect on the own row (from `s`): `crt[id]` grows, a changed own-row copy is below
the new `crt[id]` or a bare NONE copy. -/
def LStep (s t : RState) : Prop :=
  t.id = s.id ∧ t.crtInstance.length = s.crtInstance.length ∧
  sint.Z (s.crt s.id) ≤ sint.Z (t.crt s.id) ∧
  ∀ j cp, t.inst s.id j = some cp → t.inst s.id j ≠ s.inst s.id j →
    sint.Z j < sint.Z (t.crt s.id) ∨ (cp.status = St.NONE ∧ cp.lb = none)

theorem lstep_refl (s : RState) : LStep s s :=
  ⟨rfl, rfl, Int.le_refl _, fun _ _ _ h => absurd rfl h⟩

theorem lstep_frame {s t u : RState} (h : LStep s t) (e1 : u.id = t.id) (e2 : u.inst = t.inst)
    (e3 : u.crtInstance = t.crtInstance) : LStep s u := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ec : ∀ p, u.crt p = t.crt p := fun p => by simp only [RState.crt, e3]
  refine ⟨e1.trans h1, e3 ▸ h2, (ec _).symm ▸ h3, fun j cp hj hn => ?_⟩
  rw [e2] at hj hn; rw [ec]; exact h4 j cp hj hn

theorem lstep_trans {s t u : RState} (h1 : LStep s t) (h2 : LStep t u) : LStep s u := by
  obtain ⟨a1, a2, a3, a4⟩ := h1
  obtain ⟨b1, b2, b3, b4⟩ := h2
  rw [a1] at b3 b4
  refine ⟨b1.trans a1, b2.trans a2, Int.le_trans a3 b3, fun j cp hj hn => ?_⟩
  by_cases e : u.inst s.id j = t.inst s.id j
  · rw [e] at hj hn
    rcases a4 j cp hj hn with h | h
    · exact Or.inl (Int.lt_of_lt_of_le h b3)
    · exact Or.inr h
  · exact b4 j cp hj e

theorem lstep_setInst {s t : RState} {q j : w32} {c : Copy} (h : LStep s t)
    (hc : q = s.id → sint.Z j < sint.Z (t.crt s.id) ∨ (c.status = St.NONE ∧ c.lb = none)) :
    LStep s (t.setInst q j c) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun j' cp hj hn => ?_⟩
  simp only [RState.setInst] at hj hn
  by_cases e : s.id = q ∧ j' = j
  · rw [if_pos e] at hj; obtain ⟨rfl, rfl⟩ := e; cases hj; exact hc rfl
  · rw [if_neg e] at hj hn; exact h4 j' cp hj hn

theorem loc_of_lstep {s t : RState} (hL : Loc s) (h : LStep s t) : Loc t := by
  obtain ⟨l1, l2, l3⟩ := hL
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1 ▸ l1, h2.trans l2, fun j cp hj hle => ?_⟩
  rw [h1] at hj hle
  by_cases e : t.inst s.id j = s.inst s.id j
  · rw [e] at hj; exact l3 j cp hj (Int.le_trans h3 hle)
  · rcases h4 j cp hj e with h | h
    · omega
    · exact h

theorem zsucc {j : w32} (h0 : 0 ≤ sint.Z j) (h1 : sint.Z j < SLOTS) : sint.Z (j + 1) = sint.Z j + 1 := by
  unfold SLOTS at h1; word

theorem crt_setCrt (s : RState) (q x p : w32) (hq : q.toNat < s.crtInstance.length) :
    (s.setCrt q x).crt p = if q = p then x else s.crt p := by
  simp only [RState.crt, RState.setCrt, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases e : q = p
  · subst e; simp [hq]
  · have : q.toNat ≠ p.toNat := fun h => e (BitVec.eq_of_toNat_eq h)
    simp [e, this]

theorem crt_bump {s : RState} {q j : w32} (hL : Loc s) (hb : ¬ (!inBox q j) = true)
    (hge : sge j (s.crt q) = true) :
    LStep s (s.setCrt q (j + 1)) ∧ (q = s.id → sint.Z j < sint.Z ((s.setCrt q (j + 1)).crt s.id)) := by
  have hb : inBox q j = true := by cases e : inBox q j <;> simp_all
  simp only [inBox, decide_eq_true_eq] at hb
  simp only [sge, sle, decide_eq_true_eq] at hge
  have hz := zsucc (j := j) hb.2.2.1 hb.2.2.2
  have hq : q.toNat < s.crtInstance.length := by
    rw [hL.2.1]
    have h1 : sint.Z q < 3 := hb.2.1
    have h0 : 0 ≤ sint.Z q := hb.1
    word
  refine ⟨⟨rfl, by simp [RState.setCrt], ?_, ?_⟩, ?_⟩
  · rw [crt_setCrt _ _ _ _ hq]; split
    · subst_vars; omega
    · exact Int.le_refl _
  · intro j' cp hj hn; exact absurd rfl hn
  · intro e; subst e; rw [crt_setCrt _ _ _ _ hq, if_pos rfl]; omega

theorem nobump {s : RState} {q j : w32} (hlt : ¬ sge j (s.crt q) = true) :
    q = s.id → sint.Z j < sint.Z (s.crt s.id) := by
  intro e; subst e; simp only [sge, sle, decide_eq_true_eq] at hlt; omega

theorem old_lb {s : RState} {q j : w32} {c : Copy} {lb : LB} (hL : Loc s) (hc : s.inst q j = some c)
    (hlb : c.lb = some lb) : q = s.id → sint.Z j < sint.Z (s.crt s.id) := by
  intro e; subst e
  by_cases hn : sint.Z j < sint.Z (s.crt s.id)
  · exact hn
  have := (hL.2.2 j c hc (by omega)).2
  rw [hlb] at this; cases this

theorem old_st {s : RState} {q j : w32} {c : Copy} {a : w8} (hL : Loc s) (hc : s.inst q j = some c)
    (hst : ¬ c.status ≠ a) (ha : a ≠ St.NONE) : q = s.id → sint.Z j < sint.Z (s.crt s.id) := by
  intro e; subst e
  by_cases hn : sint.Z j < sint.Z (s.crt s.id)
  · exact hn
  have := (hL.2.2 j c hc (by omega)).1
  exfalso
  exact ha ((Classical.not_not.mp hst).symm.trans this)

theorem old_same {s : RState} {q j : w32} {c : Copy} (hL : Loc s) (hc : s.inst q j = some c) :
    q = s.id → sint.Z j < sint.Z (s.crt s.id) ∨ (c.status = St.NONE ∧ c.lb = none) := by
  intro e; subst e
  by_cases h : sint.Z j < sint.Z (s.crt s.id)
  · exact Or.inl h
  · exact Or.inr (hL.2.2 j c hc (by omega))

theorem rec_guard {s : RState} {q i : w32} (h : ¬ (!(rowOk q && sle 0 i && slt i (s.crt q))) = true) :
    q = s.id → sint.Z i < sint.Z (s.crt s.id) := by
  intro e; subst e
  have h' : (rowOk s.id && sle 0 i && slt i (s.crt s.id)) = true := by
    cases e : (rowOk s.id && sle 0 i && slt i (s.crt s.id)) <;> simp_all
  simp only [Bool.and_eq_true, slt, decide_eq_true_eq] at h'
  exact h'.2

theorem lstep_updCommitted {s t t' : RState} {q : w32} (h : LStep s t)
    (hu : updateCommitted t q = some t') : LStep s t' :=
  lstep_frame h (updateCommitted_inst hu).2.1 (updateCommitted_inst hu).1 (updateCommitted_inst hu).2.2
theorem lstep_updConf {s t : RState} (h : LStep s t) (cmds : List Cmd) (q i sq : w32) :
    LStep s (updateConflicts t cmds q i sq) :=
  lstep_frame h (updateConflicts_inst _ _ _ _ _).2.1 (updateConflicts_inst _ _ _ _ _).1
    (updateConflicts_inst _ _ _ _ _).2.2
theorem lstep_proposeQ {s t : RState} (h : LStep s t) (x : List Proposal) :
    LStep s { t with proposeQ := x } := h
theorem lstep_prevValTag {s t : RState} (h : LStep s t) (x : Option ValTag) :
    LStep s { t with prevValTag := x } := h

theorem leaderCommit_lstep {s t t' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit t q i c lb = .ok (t', o)) (ht : LStep s t)
    (hj : q = s.id → sint.Z i < sint.Z (t.crt s.id)) : LStep s t' := by
  unfold leaderCommit at h; peel h
  · cases h
    obtain hU := ‹updateCommitted _ _ = some _›
    refine lstep_setInst (lstep_proposeQ (lstep_updCommitted (lstep_setInst ht ?_) hU) _) ?_
    · exact fun e => Or.inl (hj e)
    · intro e; left
      have e2 := (updateCommitted_inst hU).2.2
      simp only [RState.crt, RState.setInst] at hj ⊢
      rw [e2]; exact hj e
  · cases h
    exact lstep_updCommitted (lstep_setInst ht (fun e => Or.inl (hj e))) ‹updateCommitted _ _ = some _›

theorem startPhase1_lstep {s t t' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 t q i b ps cs = .ok (t', o)) (ht : LStep s t)
    (hj : q = s.id → sint.Z i < sint.Z (t.crt s.id)) : LStep s t' := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; exact lstep_updConf (lstep_setInst ht (fun e => Or.inl (hj e))) _ _ _ _)

set_option maxRecDepth 20000
theorem crt_setInst (s : RState) (q i : w32) (c : Copy) (p : w32) : (s.setInst q i c).crt p = s.crt p := rfl

theorem side_bump {s : RState} {q j : w32} (hL : Loc s) (hb : ¬ (!inBox q j) = true)
    (hge : sge j (s.crt q) = true) (hq : q = s.id) (t : RState)
    (ht : t.crtInstance = (s.setCrt q (j + 1)).crtInstance) : sint.Z j < sint.Z (t.crt s.id) := by
  have : t.crt s.id = (s.setCrt q (j + 1)).crt s.id := by simp only [RState.crt, ht]
  rw [this]; exact (crt_bump hL hb hge).2 hq
theorem side_nobump {s : RState} {q j : w32} (hlt : ¬ sge j (s.crt q) = true) (hq : q = s.id)
    (t : RState) (ht : t.crtInstance = s.crtInstance) : sint.Z j < sint.Z (t.crt s.id) := by
  have : t.crt s.id = s.crt s.id := by simp only [RState.crt, ht]
  rw [this]; exact nobump hlt hq
theorem side_lb {s : RState} {q j : w32} {c : Copy} {lb : LB} (hL : Loc s) (hc : s.inst q j = some c)
    (hlb : c.lb = some lb) (hq : q = s.id) (t : RState) (ht : t.crtInstance = s.crtInstance) :
    sint.Z j < sint.Z (t.crt s.id) := by
  have : t.crt s.id = s.crt s.id := by simp only [RState.crt, ht]
  rw [this]; exact old_lb hL hc hlb hq
theorem side_st {s : RState} {q j : w32} {c : Copy} {a : w8} (hL : Loc s) (hc : s.inst q j = some c)
    (hst : ¬ c.status ≠ a) (ha : a ≠ St.NONE) (hq : q = s.id) (t : RState)
    (ht : t.crtInstance = s.crtInstance) : sint.Z j < sint.Z (t.crt s.id) := by
  have : t.crt s.id = s.crt s.id := by simp only [RState.crt, ht]
  rw [this]; exact old_st hL hc hst ha hq
theorem side_same {s : RState} {q j : w32} {c c' : Copy} (hL : Loc s) (hc : s.inst q j = some c)
    (e1 : c'.status = c.status) (e2 : c'.lb = c.lb) (hq : q = s.id) (t : RState)
    (ht : t.crtInstance = s.crtInstance) :
    sint.Z j < sint.Z (t.crt s.id) ∨ (c'.status = St.NONE ∧ c'.lb = none) := by
  have : t.crt s.id = s.crt s.id := by simp only [RState.crt, ht]
  rw [this, e1, e2]; exact old_same hL hc hq
theorem side_rec {s : RState} {q i : w32} (h : ¬ (!(rowOk q && sle 0 i && slt i (s.crt q))) = true)
    (hq : q = s.id) (t : RState) (ht : t.crtInstance = s.crtInstance) : sint.Z i < sint.Z (t.crt s.id) := by
  have : t.crt s.id = s.crt s.id := by simp only [RState.crt, ht]
  rw [this]; exact rec_guard h hq

macro "asm" : term => `((by with_reducible assumption))

macro "lside" : tactic => `(tactic| (first
    | exact fun _ => Or.inr ⟨rfl, rfl⟩
    | exact fun hq => Or.inl (side_bump asm asm asm hq _ (by rfl))
    | exact fun hq => Or.inl (side_nobump asm hq _ (by rfl))
    | exact fun hq => Or.inl (side_lb asm asm asm hq _ (by rfl))
    | exact fun hq => Or.inl (side_st asm asm asm (by decide) hq _ (by rfl))
    | exact fun hq => side_same asm asm (by rfl) (by rfl) hq _ (by rfl)
    | exact fun hq => Or.inl (side_rec asm hq _ (by rfl))
    | (split <;> exact fun hq => side_same asm asm (by rfl) (by rfl) hq _ (by rfl))
    | exact fun hq => side_lb asm asm asm hq _ (by rfl)
    | exact fun hq => side_st asm asm asm (by decide) hq _ (by rfl)))


macro "lstep_fin" : tactic => `(tactic| (
  repeat (first
    | exact lstep_refl _
    | (apply lstep_updCommitted ?_ ‹updateCommitted _ _ = some _›)
    | apply lstep_updConf
    | apply lstep_setInst
    | apply lstep_proposeQ
    | apply lstep_prevValTag
    | exact (crt_bump asm asm asm).1)
  all_goals lside))

macro "lstep_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; lstep_fin; done)
    | (refine leaderCommit_lstep $h:ident ?_ ?_ <;> lstep_fin; done)
    | (refine startPhase1_lstep $h:ident ?_ ?_ <;> lstep_fin; done))))

theorem stepPreAccept_lstep {s s' : RState} {m : PreAcceptM} {o : List Out} (hL : Loc s)
    (h : stepPreAccept s m = .ok (s', o)) : LStep s s' := by
  unfold stepPreAccept at h; lstep_close h
theorem stepAccept_lstep {s s' : RState} {m : EAcceptM} {o : List Out} (hL : Loc s)
    (h : stepAccept s m = .ok (s', o)) : LStep s s' := by
  unfold stepAccept at h; lstep_close h
theorem stepCommit_lstep {s s' : RState} {m : ECommitM} {o : List Out} (hL : Loc s)
    (h : stepCommit s m = .ok (s', o)) : LStep s s' := by
  unfold stepCommit at h; lstep_close h
theorem stepPreAcceptReply_lstep {s s' : RState} {m : PreAcceptReplyM} {o : List Out} (hL : Loc s)
    (h : stepPreAcceptReply s m = .ok (s', o)) : LStep s s' := by
  unfold stepPreAcceptReply at h; lstep_close h
theorem stepPreAcceptOK_lstep {s s' : RState} {m : PreAcceptOKM} {o : List Out} (hL : Loc s)
    (h : stepPreAcceptOK s m = .ok (s', o)) : LStep s s' := by
  unfold stepPreAcceptOK at h; lstep_close h
theorem stepAcceptReply_lstep {s s' : RState} {m : AcceptReplyM} {o : List Out} (hL : Loc s)
    (h : stepAcceptReply s m = .ok (s', o)) : LStep s s' := by
  unfold stepAcceptReply at h; lstep_close h
theorem stepPrepare_lstep {s s' : RState} {m : PrepareM} {o : List Out} (hL : Loc s)
    (h : stepPrepare s m = .ok (s', o)) : LStep s s' := by
  unfold stepPrepare at h; lstep_close h
theorem stepPrepareReply_lstep {s s' : RState} {m : PrepareReplyM} {o : List Out} (hL : Loc s)
    (h : stepPrepareReply s m = .ok (s', o)) : LStep s s' := by
  unfold stepPrepareReply at h; lstep_close h
theorem handleExecuted_lstep {s s' : RState} {m : ExecutedM} {o : List Out} (hL : Loc s)
    (h : handleExecuted s m = .ok (s', o)) : LStep s s' := by
  unfold handleExecuted at h; lstep_close h
theorem stepRecover_lstep {s s' : RState} {q i : w32} {o : List Out} (hL : Loc s)
    (h : stepRecover s q i = .ok (s', o)) : LStep s s' := by
  unfold stepRecover at h; lstep_close h
theorem stepExec_lstep {s s' : RState} {q i : w32} {o : List Out} (hL : Loc s)
    (h : stepExec s q i = .ok (s', o)) : LStep s s' := by
  unfold stepExec at h; lstep_close h

/-! ## The handlers left: client RMWs, executor results; every step; along a replica's run -/

set_option maxRecDepth 20000

theorem handlePropose_lk {s s' : RState} {p : Proposal} {o : List Out} (hL : Loc s)
    (h : handlePropose s p = .ok (s', o)) : LStep s s' ∧ ExecKeep s s' := by
  obtain ⟨-, -, h⟩ := handlePropose_ok h; unfold handleProposeBody startPhase1 at h; peel h
  all_goals (
    cases h
    have hge : sge (s.crt s.id) (s.crt s.id) = true := by simp [sge, sle]
    have hb := (crt_bump hL ‹¬ (!inBox _ _) = true› hge)
    constructor
    · apply lstep_updConf; apply lstep_setInst; apply lstep_proposeQ; exact hb.1
      exact fun hq => Or.inl (hb.2 hq)
    · apply keep_updConf; apply keep_setInst; apply keep_proposeQ; exact keep_setCrt (keep_refl _) _ _
      intro c0 hc0 hex
      have := (hL.2.2 _ c0 hc0 (Int.le_refl _)).1
      rw [hex] at this; exact absurd this (by decide))

theorem stepClientRMW_lk {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    {o : List Out} (hL : Loc s) (h : stepClientRMW s rid cid k d a b = .ok (s', o)) :
    LStep s s' ∧ ExecKeep s s' := by
  unfold stepClientRMW at h; peel h
  exact handlePropose_lk (s := { s with nReqs := s.nReqs + 1, used := (cid, rid) :: s.used }) hL h

theorem stepExecuteOverwrite_lk {s s' : RState} {m : ExecuteOverwriteM} {o : List Out} (hL : Loc s)
    (h : stepExecuteOverwrite s m = .ok (s', o)) : LStep s s' ∧ ExecKeep s s' := by
  have hf := overwrite_frame s m.v m.t
  have hL' : Loc (s.overwrite m.v m.t) := by
    unfold Loc; rw [hf.1, hf.2.1]; simp only [RState.crt, hf.2.2]; exact hL
  have hs : LStep s (s.overwrite m.v m.t) ∧ ExecKeep s (s.overwrite m.v m.t) :=
    ⟨lstep_frame (lstep_refl s) hf.1 hf.2.1 hf.2.2, keep_inst (keep_refl s) hf.2.1⟩
  unfold stepExecuteOverwrite at h; peel h
  · exact ⟨lstep_trans hs.1 (handleExecuted_lstep hL' h), keep_trans hs.2 (handleExecuted_keep h)⟩
  · cases h; exact hs

theorem frame_lk {s s' : RState} (h : Frame s s') : LStep s s' ∧ ExecKeep s s' :=
  ⟨lstep_frame (lstep_refl s) h.1 h.2.1 h.2.2, keep_inst (keep_refl s) h.2.1⟩

/-- Every step keeps the own row's shape and keeps EXECUTED copies. -/
theorem step_lk {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out} (hL : Loc s)
    (h : stepR r s e = .ok (s', o)) : LStep s s' ∧ ExecKeep s s' := by
  cases e with
  | read => exact frame_lk (stepClientRead_frame h)
  | write => exact frame_lk (stepClientWrite_frame h)
  | rmw => exact stepClientRMW_lk hL h
  | forceWrite => cases h; exact ⟨lstep_refl _, keep_refl _⟩
  | recover => exact ⟨stepRecover_lstep hL h, stepRecover_keep h⟩
  | exec => exact ⟨stepExec_lstep hL h, stepExec_keep h⟩
  | msg m =>
    cases m with
    | read1 => exact frame_lk (stepRead1_frame h)
    | read2 => exact frame_lk (stepRead2_frame h)
    | write1 => exact frame_lk (stepWrite1_frame h)
    | write2 => exact frame_lk (stepWrite2_frame h)
    | read1Reply => exact frame_lk (stepRead1Reply_frame h)
    | read2Reply => exact frame_lk (stepRead2Reply_frame h)
    | write1Reply => exact frame_lk (stepWrite1Reply_frame h)
    | write2Reply => exact frame_lk (stepWrite2Reply_frame h)
    | prepare => exact ⟨stepPrepare_lstep hL h, stepPrepare_keep h⟩
    | preAccept => exact ⟨stepPreAccept_lstep hL h, stepPreAccept_keep h⟩
    | accept => exact ⟨stepAccept_lstep hL h, stepAccept_keep h⟩
    | commit => exact ⟨stepCommit_lstep hL h, stepCommit_keep h⟩
    | prepareReply => exact ⟨stepPrepareReply_lstep hL h, stepPrepareReply_keep h⟩
    | preAcceptReply => exact ⟨stepPreAcceptReply_lstep hL h, stepPreAcceptReply_keep h⟩
    | preAcceptOK => exact ⟨stepPreAcceptOK_lstep hL h, stepPreAcceptOK_keep h⟩
    | acceptReply => exact ⟨stepAcceptReply_lstep hL h, stepAcceptReply_keep h⟩
    | executed => exact ⟨handleExecuted_lstep hL h, handleExecuted_keep h⟩
    | executeOverwrite => exact stepExecuteOverwrite_lk hL h

theorem loc_init (r : Fin 3) : Loc (RState.init r.val) := by
  refine ⟨?_, rfl, fun j cp h _ => by cases h⟩
  show (BitVec.ofNat 32 r.val).toNat < 3
  have := r.isLt; simp; omega

theorem gstep_ok {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : gNet.step r s e = some (s', o)) : stepR r s e = .ok (s', o) := by
  change gStep r s e = some (s', o) at h
  unfold gStep at h
  cases hres : stepR r s e with
  | error f => rw [hres] at h; cases h
  | ok p => rw [hres] at h; cases h; rfl

/-- Along one replica's run: `Loc` holds. -/
theorem runP_loc {r : Fin 3} {es : List Ev} {s : RState} {o : List Out}
    (h : kahn.runP gNet r es = some (s, o)) : Loc s := by
  induction es using snoc_ind generalizing s o with
  | h0 => cases h; exact loc_init r
  | hs es e ih =>
    obtain ⟨s1, o1, o2, h1, h2, -⟩ := kahn.runFrom_append_inv h
    have h2' : gNet.step r s1 e = some (s, o2) := (kahn.runFrom_single r s1 e).symm.trans h2
    exact loc_of_lstep (ih h1) (step_lk (ih h1) (gstep_ok h2')).1

open kahn in
theorem runP_take {r : Fin 3} {es : List Ev} {s : RState} {o : List Out}
    (h : runP gNet r es = some (s, o)) (j : Nat) : ∃ s1 o1, runP gNet r (es.take j) = some (s1, o1) := by
  rw [← List.take_append_drop j es] at h
  obtain ⟨s1, o1, -, h1, -, -⟩ := runFrom_append_inv h
  exact ⟨s1, o1, h1⟩

open kahn in
/-- Event `j` of a replica's run steps from the state after the first `j` events to the state after
the first `j + 1`. -/
theorem runP_step {r : Fin 3} {es : List Ev} {s : RState} {o : List Out}
    (h : runP gNet r es = some (s, o)) {j : Nat} {e : Ev} (hj : es[j]? = some e) :
    ∃ o', stepR r (stOf r (es.take j)) e = .ok (stOf r (es.take (j + 1)), o') := by
  obtain ⟨s2, o2, h2⟩ := runP_take h (j + 1)
  have et : es.take (j + 1) = es.take j ++ [e] := by rw [List.take_add_one, hj]; rfl
  have h2' : runP gNet r (es.take j ++ [e]) = some (s2, o2) :=
    (congrArg (runP gNet r) et).symm.trans h2
  obtain ⟨s1, o1, o', h1, h3, -⟩ := runFrom_append_inv h2'
  have h3' : gNet.step r s1 e = some (s2, o') := (runFrom_single r s1 e).symm.trans h3
  have e1 : stOf r (es.take j) = s1 := stOf_of_runP h1
  have e2 : stOf r (es.take (j + 1)) = s2 := by
    exact stOf_of_runP h2
  rw [e1, e2]; exact ⟨o', gstep_ok h3'⟩

theorem runP_keep {r : Fin 3} {es : List Ev} {s : RState} {o : List Out}
    (h : kahn.runP gNet r es = some (s, o)) {j k : Nat} (hjk : j ≤ k) (hk : k ≤ es.length) :
    ExecKeep (stOf r (es.take j)) (stOf r (es.take k)) := by
  induction k with
  | zero => have : j = 0 := by omega
            subst this; exact keep_refl _
  | succ k ih =>
    by_cases e : j = k + 1
    · subst e; exact keep_refl _
    have hk' : k < es.length := by omega
    obtain ⟨o', hs⟩ := runP_step h (List.getElem?_eq_getElem hk')
    obtain ⟨s1, o1, h1⟩ := runP_take h k
    have hL : Loc (stOf r (es.take k)) := (stOf_of_runP h1) ▸ runP_loc h1
    exact keep_trans (ih (by omega) (by omega)) (step_lk hL hs).2

theorem stepExec_facts {s s' : RState} {q i : w32} {o : List Out} (h : stepExec s q i = .ok (s', o)) :
    (∃ c, s.inst q i = some c ∧ c.status = St.COMMITTED) ∧
      ∃ c, s'.inst q i = some c ∧ c.status = St.EXECUTED := by
  unfold stepExec at h; peel h
  all_goals (
    cases h
    refine ⟨⟨_, ‹_›, by simpa using ‹¬ _ ≠ St.COMMITTED›⟩, ?_⟩
    simp [setInst_inst])

/-- **A replica executes an instance at most once**: once event `j1` (an `exec (q, i)`) succeeded,
a later `exec (q, i)` does not. -/
theorem exec_twice {r : Fin 3} {es : List Ev} {s : RState} {o : List Out}
    (h : kahn.runP gNet r es = some (s, o)) {j1 j2 : Nat} {q i : w32} (hlt : j1 < j2)
    (e1 : es[j1]? = some (.exec q i)) (e2 : es[j2]? = some (.exec q i)) :
    ∀ x, stepR r (stOf r (es.take j2)) (.exec q i) ≠ .ok x := by
  intro ⟨s2, o2⟩ h2
  obtain ⟨o', h1⟩ := runP_step h e1
  have hj2 : j2 < es.length := (List.getElem?_eq_some_iff.1 e2).1
  obtain ⟨-, c1, hc1, hx1⟩ := stepExec_facts h1
  obtain ⟨c2, hc2, hx2⟩ := runP_keep h (j := j1 + 1) (k := j2) (by omega) (by omega) q i c1 hc1 hx1
  obtain ⟨⟨c3, hc3, hx3⟩, -⟩ := stepExec_facts h2
  rw [hc2] at hc3; cases hc3
  rw [hx2] at hx3; exact absurd hx3 (by decide)

end Perennial.gryff.pureA
