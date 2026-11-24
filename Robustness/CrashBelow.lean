/-
The bridge from the single-node crash adequacy theorem with the thread bound along the execution
(Perennial's `goose_crash_adequacy_below`, `AdequacyAlong.lean`) to the robustness statement
(`Robustness/Statement.lean`): `Robust.of_single_crashing_below`, the analogue of
`Robust.of_single_crashing` that keeps the thread bound, as `Robust.of_single_below` does for a
process that never crashes. A module of its own so that the statement's importers do not rebuild.
-/
module

public import Robustness.Statement

@[expose] public section

noncomputable section

namespace Perennial
namespace Robustness

open Iris.ProgramLogic

section facts
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- A real step, from a configuration with fewer than `T` threads, before an execution with
crashes of one process along which fewer than `T` threads are live. -/
theorem realCrashNstepsBelow_step {boot : Expr} {T m : Nat} {ρ₁ ρ₂ ρ' : List Expr × CfgState}
    {κ κs : List Observation} {b : Bool} (hlt : ρ₁.2.1.threads < T)
    (hs : @Language.Step _ _ _ _ gooseRealLang ρ₁ κ ρ₂) (h : RealCrashNstepsBelow boot T m ρ₂ κs ρ' b) :
    RealCrashNstepsBelow boot T (m + 1) ρ₁ (κ ++ κs) ρ' b := by
  cases h with
  | done h => exact .done (.cons hlt hs h)
  | @crash n₁ m₂ _ κs₁ t σ g σ' κs₂ _ b' h₁ hc h₂ =>
    have h₃ := RealCrashNstepsBelow.crash (boot := boot) (.cons hlt hs h₁) hc h₂
    rw [List.append_assoc] at h₃
    rw [show n₁ + m₂ + 1 = n₁ + 1 + m₂ by omega]
    exact h₃

/-- One machine with a boot program, with the thread bound: its executions are those of a single
process with crashes along which fewer than `T` threads are live (`RealCrashNstepsBelow`; a crash
is not a step there, so of at most as many steps). -/
theorem distCrashNstepsBelow_single_crashing {boot : Expr} {T n : Nat} {tp : List Expr}
    {σ : state} {g : GlobalState} {κs : List Observation} {c : DistCfg}
    (h : DistCrashNstepsBelow [boot] T n ⟨[(tp, σ)], g⟩ κs c) :
    ∃ tp' σ' g' m b, m ≤ n ∧ c = ⟨[(tp', σ')], g'⟩ ∧
      RealCrashNstepsBelow boot T m (tp, (σ, g)) κs (tp', (σ', g')) b := by
  generalize hc₀ : (⟨[(tp, σ)], g⟩ : DistCfg) = c₀ at h
  induction h generalizing tp σ g with
  | refl c hc =>
    subst hc₀
    exact ⟨tp, σ, g, 0, false, Nat.le_refl _, rfl, .done (.refl _ (hc 0 tp σ rfl))⟩
  | @cons n c₁ c₂ c₃ κ κs hc hstep _ ih =>
    subst hc₀
    cases hstep with
    | @crash nodes g i tp₀ σ₀ e σ₁ hi hb hcr =>
      obtain rfl : i = 0 := by
        have := (List.getElem?_eq_some_iff.mp hi).1
        simp only [List.length_singleton] at this
        omega
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi hb
      obtain ⟨rfl, rfl⟩ := hi
      subst hb
      obtain ⟨tp', σ', g', m, b, hm, rfl, hrest⟩ := ih (tp := [boot]) (σ := σ₁) (g := g) rfl
      refine ⟨tp', σ', g', 0 + m, true, by omega, rfl, ?_⟩
      exact .crash (.refl _ (hc 0 _ _ rfl)) hcr hrest
    | step hstep =>
      cases hstep with
      | @node nodes g i tp₀ σ₀ κ tp₁ σ₁ g₁ hi hs =>
        obtain rfl : i = 0 := by
          have := (List.getElem?_eq_some_iff.mp hi).1
          simp only [List.length_singleton] at this
          omega
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        obtain ⟨tp', σ', g', m, b, hm, rfl, hrest⟩ := ih (tp := tp₁) (σ := σ₁) (g := g₁) rfl
        exact ⟨tp', σ', g', m + 1, b, by omega, rfl,
          realCrashNstepsBelow_step (hc 0 _ _ rfl) hs hrest⟩

/-- **A single process that crashes and restarts, with its thread bound**: the conclusion of
`goose_crash_adequacy_below` (Perennial's `AdequacyAlong.lean`: in every real execution with
crashes of fewer than `bound` steps along which fewer than `threads` threads are live, no thread
stuck, none with an unrecovered panic) is the robustness statement of the program alone on a
machine that may crash, at that thread bound. -/
theorem Robust.of_single_crashing_below [lctx : GoLocalContext] {e : Expr} {σ : state}
    {g : GlobalState} {threads bound : Nat}
    (h : Fresh lctx σ →
      ∀ (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool),
      n < bound → RealCrashNstepsBelow e threads n ([e], ((σ, g) : CfgState)) κs (t2, σ2) b →
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧ (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)) :
    Robust [(e, σ)] [] g threads bound := by
  intro hfresh _ _ n κs c hsteps hn i tp' σ' hi e' he'
  obtain ⟨tp₁, σ₁, g₁, m, b, hm, rfl, hreal⟩ :=
    distCrashNstepsBelow_single_crashing (boot := e) (tp := [e]) hsteps
  obtain ⟨hns, hnp⟩ := h (hfresh (e, σ) (by simp)) m κs tp₁ (σ₁, g₁) b (by omega) hreal
  obtain rfl : i = 0 := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_singleton] at this
    omega
  simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
  obtain ⟨rfl, rfl⟩ := hi
  exact ⟨hns e' he', hnp e' he'⟩

end facts

end Robustness
end Perennial

end
