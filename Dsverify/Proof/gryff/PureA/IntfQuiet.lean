/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/IntfQuiet.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AI, internal: the steps that touch no conflict table nor (but by `CopySim`) any copy: the Gryff
handlers, the execution, `handleExecuted`, `ExecuteOverwrite`: the table is unchanged (per handler,
as A1's `Frame` lemmas) and the local obligations hold (`stepI_frame`, `stepI_sim`).
-/
module

public import Dsverify.Proof.gryff.PureA.IntfSteps4

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AI

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA
open Perennial.gryff.pureA.AW

variable {rc : RecG} {κ : Nat} {dg : DepG} {s s' : RState} {a : Fin 3} {o : List Out}

/-! ## The table -/

theorem shortCircuit_conf {n : w32} {v : ValTag} {f : Bool}
    (h : shortCircuit s n v f = some (s', o)) : s'.conf = s.conf := by
  rcases Perennial.gryff.model.shortCircuit_cases h with h | ⟨rfl, rfl⟩
  rotate_left
  · rfl
  unfold Perennial.gryff.model.shortCircuitReads at h
  opeel h
  all_goals
    cases h
    refine forIn_opt_invA _ _ _ (fun p : RState × List Out => p.1.conf = s.conf) rfl ?_ _ ‹_›
    intro a b st hb hf
    opeel hf
    all_goals (cases hf; exact hb)

theorem shortCircuit_ite_conf {c : Prop} [Decidable c] {n : w32} {v : ValTag} {f : Bool}
    (h : (if c then shortCircuit s n v f else some (s, [])) = some (s', o)) : s'.conf = s.conf := by
  split at h
  · exact shortCircuit_conf h
  · cases h; rfl

macro "cf_fin" : tactic => `(tactic| (
  try (have hsc := shortCircuit_conf ‹shortCircuit _ _ _ _ = some _›)
  try (have hsc := shortCircuit_ite_conf ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›)
  simp only [overwrite_conf] <;> first | rfl | assumption))

macro "cf_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (cases $h:ident; cf_fin)))

theorem stepRead1_conf {m : Read1ProxiedM} (h : stepRead1 s m = .ok (s', o)) : s'.conf = s.conf := by
  unfold stepRead1 at h; cf_close h
theorem stepRead2_conf {m : Read2ProxiedM} (h : stepRead2 s m = .ok (s', o)) : s'.conf = s.conf := by
  unfold stepRead2 at h; cf_close h
theorem stepWrite1_conf {m : Write1ProxiedM} (h : stepWrite1 s m = .ok (s', o)) : s'.conf = s.conf := by
  unfold stepWrite1 at h; cf_close h
theorem stepWrite2_conf {m : Write2ProxiedM} (h : stepWrite2 s m = .ok (s', o)) : s'.conf = s.conf := by
  unfold stepWrite2 at h; cf_close h
theorem stepRead1Reply_conf {m : Read1ReplyM} (h : stepRead1Reply s m = .ok (s', o)) :
    s'.conf = s.conf := by
  unfold stepRead1Reply at h; cf_close h
theorem stepRead2Reply_conf {m : Read2ReplyM} (h : stepRead2Reply s m = .ok (s', o)) :
    s'.conf = s.conf := by
  unfold stepRead2Reply at h; cf_close h
theorem stepWrite1Reply_conf {m : Write1ReplyM} (h : stepWrite1Reply s m = .ok (s', o)) :
    s'.conf = s.conf := by
  unfold stepWrite1Reply at h; cf_close h
theorem stepWrite2Reply_conf {m : Write2ReplyM} (h : stepWrite2Reply s m = .ok (s', o)) :
    s'.conf = s.conf := by
  unfold stepWrite2Reply at h; cf_close h
theorem stepClientWrite_conf {rid cid : w32} {k v : w64} {d : Dep}
    (h : stepClientWrite s rid cid k v d = .ok (s', o)) : s'.conf = s.conf := by
  unfold stepClientWrite at h; cf_close h
theorem stepClientRead_conf {rid cid : w32} {k : w64} {d : Dep}
    (h : stepClientRead s rid cid k d = .ok (s', o)) : s'.conf = s.conf := by
  unfold stepClientRead at h
  peel h
  cases h
  have hx := ‹forIn _ _ _ = Except.ok s'›
  refine forIn_exc_invA _ _ _ (fun x : RState => x.conf = s.conf) ?_ ?_ _ hx
  · rfl
  intro a b st hb hf
  peel hf
  all_goals (cases hf; exact hb)

theorem stepExec_conf {q i : w32} (h : stepExec s q i = .ok (s', o)) : s'.conf = s.conf := by
  unfold stepExec at h; peel h
  all_goals (cases h; rfl)

theorem handleExecuted_conf {m : ExecutedM} (h : handleExecuted s m = .ok (s', o)) :
    s'.conf = s.conf := by
  unfold handleExecuted at h; peel h
  all_goals (cases h; rfl)

theorem stepExecuteOverwrite_conf {m : ExecuteOverwriteM}
    (h : stepExecuteOverwrite s m = .ok (s', o)) : s'.conf = s.conf := by
  unfold stepExecuteOverwrite at h; peel h
  · rw [handleExecuted_conf h, overwrite_conf]
  · cases h; exact overwrite_conf _ _ _

/-! ## The local obligations -/

theorem msgI_quiet {d : Fin 3} {m : Msg} (h : isEp m = false) : MsgI rc κ dg d m := by
  cases m <;> first | trivial | cases h

theorem stepI_frame (hf : Frame s s') (hc : s'.conf = s.conf) (ho : QuietO o) :
    StepI rc κ dg s s' a o none :=
  ⟨confLe_of_eq hc, by simp only [RState.crt, hf.2.2, hf.1],
    fun _ _ h => (by cases h),
    fun q i cp h => Or.inl (by rw [← hf.2.1]; exact h),
    fun _ _ hm => msgI_quiet (sentR_quiet ho hm)⟩

theorem copyI_sim {rc' : RecG} {κ' : Nat} {q i : w32} {cp cp' : Copy}
    (h : CopyI rc' κ' dg q i a cp) (hs : CopySim cp cp') : CopyI rc' κ' dg q i a cp' := by
  have hv := hs.valA
  simp only [Copy.valA, Prod.mk.injEq] at hv
  obtain ⟨e1, -, e3, -⟩ := hv
  have hst : cp'.status = cp.status ∨ (cp.status = St.COMMITTED ∧ cp'.status = St.EXECUTED) := hs.st
  refine ⟨fun h1 h2 => ?_, fun h1 h2 h3 h4 => ?_, fun lb hl hn => ?_⟩
  · rw [e1] at h1; rw [e3]
    rcases hst with e | ⟨e, e'⟩
    · rw [e] at h2 ⊢; exact h.val h1 h2
    · obtain ⟨⟨k1, k2, k3⟩, -⟩ := h.val h1 (by rw [e]; decide)
      refine ⟨⟨k1, k2, fun _ => k3 (by rw [e]; exact strong_com)⟩, fun he => ?_⟩
      rw [e'] at he; exact absurd he (by decide)
  · rw [e1] at h1; rw [e3]
    rcases hst with e | ⟨e, e'⟩
    · rw [e] at h4; rw [hs.ballot] at h3; exact h.own0 h1 h2 h3 h4
    · rw [e'] at h4; exact absurd h4 (by decide)
  · obtain ⟨l0, hl0, el⟩ := hs.lb_some hl
    have hn' : ¬ isCommitted cp.status := by
      rcases hst with e | ⟨e, e'⟩
      · rw [← e]; exact hn
      · exact absurd (Or.inr e') hn
    have := h.cand l0 hl0 hn'
    rw [← el.2.1]; exact this

theorem stepI_sim (C : CtxI rc κ dg s a) (hf : SimFrame s s') (hc : s'.conf = s.conf)
    (ho : QuietO o) : StepI rc κ dg s s' a o none := by
  refine ⟨confLe_of_eq hc, by simp only [RState.crt, hf.2.1, hf.1], fun _ _ h => (by cases h),
    fun q i cp h => Or.inr ?_, fun _ _ hm => msgI_quiet (sentR_quiet ho hm)⟩
  have hs := hf.2.2 q i
  rw [h] at hs
  obtain ⟨cp0, h0, hsim⟩ := OSim.some_r hs
  exact copyI_sim (cM (C.copies q i cp0 h0)) hsim

end Perennial.gryff.pureA.AI
