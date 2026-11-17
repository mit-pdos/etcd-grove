/-
The statement of a robustness theorem [Trusted definition!]: one definition, over the executions
of Perennial's distributed semantics (`Perennial/GooseLang/DistLang.lean`), for any extensions.

`Robust crashing stable g bound`: run the programs of `crashing`, each on a machine of its own
that may crash at any step and then restarts with its program (from a local state its extensions'
crash relations allow), and the programs of `stable`, each on a machine of its own that never
crashes, all sharing the global state `g` (the network, with whatever extensions are plugged in:
`[GooseExts] [GooseSemantics]`). Then, in every execution of fewer than `bound` steps, no thread
of any machine has a panic that nothing recovered (a top-level panic), and none is stuck (which
is what an invalid operation is in GooseLang, its builtin `Panic` among them: the conclusion of
the adequacy theorems, `goose_dist_crash_adequacy`).

The executions are `DistCrashNsteps`, Perennial's: a real step of one thread of one machine, or a
crash of a machine that has a boot program. Its list of boot programs is `crashing`'s, so the
machines of `stable`, which come after them, have none and never crash (`distCrashStep_cases`).
Everything else is that relation's nondeterminism: the scheduler (a machine that never runs
again, or starts late, is one it does not pick), the crashes, and the faults the extensions'
semantics allow (the TCP extension: a direction cut at any read or write, any delay, a dial
failing; a partition is such an execution).

**Every machine starts as a fresh Go process** (`Fresh`, a premise inside `Robust`, so that no
instance repeats it): its Go context is the one the theorem's Go semantics is about (`lctx`, the
instance `[GoLocalContext]`: the meaning of the Go instructions, shared by the machines as echo's
three programs share one), no package is initialized, and it has its main thread only. What an
extension needs of a start state (no connection, a file system's roots) stays the instance's.

The statement says nothing of what the programs compute. A property of a system (its clients'
history is linearizable) is a theorem of this form about a deployment that includes a program
checking it and panicking if it fails, e.g. a client on a machine that does not crash, which
keeps its history: the property is then written in Go, where it is tested, and not in a trusted
Lean definition over traces.

The step bound is the proofs' (time receipts, as the closed adequacy theorems' `n < 2^61`).
-/
module

public import Perennial.GooseLang.DistLang

@[expose] public section

noncomputable section

namespace Perennial
namespace Robustness

open Iris.ProgramLogic

section statement
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- The machine with the local state `σ` is a fresh Go process with the Go context `lctx`: no
package initialized, its main thread only. -/
def Fresh (lctx : GoLocalContext) (σ : state) : Prop :=
  σ.goState.goLctx = lctx ∧ σ.goState.packageState = ∅ ∧ σ.threads = 1

/-- **A robustness statement** (see the file header): in every execution of fewer than `bound`
steps of the machines `crashing` (which may crash and restart) and `stable` (which never crash),
each running its program from its local state, a fresh Go process with the context `lctx`, on
the shared state `g`, no thread of any machine is stuck or has an unrecovered panic. -/
def Robust [lctx : GoLocalContext] (crashing stable : List (Expr × state)) (g : GlobalState)
    (bound : Nat) : Prop :=
  (∀ m, m ∈ crashing ++ stable → Fresh lctx m.2) →
  ∀ (n : Nat) (κs : List Observation) (c : DistCfg),
    DistCrashNsteps (crashing.map Prod.fst) n (distInit (crashing ++ stable) g) κs c →
    n < bound →
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      ∀ e, e ∈ tp → RealNotStuck e (σ, c.global) ∧ ¬ UnrecoveredPanic e

end statement

/-! ## Sanity -/

section facts
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- A step of the executions is a step of a thread, or a crash of one of the first
`boots.length` machines: a machine after them never crashes. -/
theorem distCrashStep_cases {boots : List Expr} {c c' : DistCfg} {κ : List Observation}
    (h : DistCrashStep boots c κ c') :
    DistStep c κ c' ∨
      ∃ i tp σ e σ', i < boots.length ∧ c.nodes[i]? = some (tp, σ) ∧ boots[i]? = some e ∧
        Crash σ σ' ∧ c' = ⟨c.nodes.set i ([e], σ'), c.global⟩ := by
  cases h with
  | step h => exact .inl h
  | @crash nodes g i tp σ e σ' hi hb hc =>
    exact .inr ⟨i, tp, σ, e, σ', (List.getElem?_eq_some_iff.mp hb).1, hi, hb, hc, rfl⟩

/-- Letting more machines crash only adds executions. -/
theorem distCrashNsteps_more_boots {boots : List Expr} (rest : List Expr) {n : Nat}
    {c c' : DistCfg} {κs : List Observation} (h : DistCrashNsteps boots n c κs c') :
    DistCrashNsteps (boots ++ rest) n c κs c' := by
  induction h with
  | refl c => exact .refl c
  | cons hs _ ih =>
    refine .cons ?_ ih
    cases hs with
    | step hs => exact .step hs
    | crash hi hb hc =>
      refine .crash hi ?_ hc
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hb).1]
      exact hb

/-- A deployment that is robust when every machine may crash is robust when only some may: the
distributed crash adequacy theorem (`goose_dist_crash_adequacy`, about executions in which every
node may crash) proves statements of this form. -/
theorem Robust.of_all_crashing [GoLocalContext] {crashing stable : List (Expr × state)}
    {g : GlobalState} {bound : Nat} (h : Robust (crashing ++ stable) [] g bound) :
    Robust crashing stable g bound := by
  intro hfresh n κs c hsteps hn
  refine h (by simpa using hfresh) n κs c ?_ hn
  rw [List.map_append, List.append_nil]
  exact distCrashNsteps_more_boots _ hsteps

/-- One machine with no boot program runs as a single process: its executions are the real
thread-pool executions (`RealNsteps`) of its threads. -/
theorem distCrashNsteps_single {n : Nat} {tp : List Expr} {σ : state} {g : GlobalState}
    {κs : List Observation} {c : DistCfg}
    (h : DistCrashNsteps [] n ⟨[(tp, σ)], g⟩ κs c) :
    ∃ tp' σ' g', c = ⟨[(tp', σ')], g'⟩ ∧ RealNsteps n (tp, (σ, g)) κs (tp', (σ', g')) := by
  generalize hc₀ : (⟨[(tp, σ)], g⟩ : DistCfg) = c₀ at h
  induction h generalizing tp σ g with
  | refl c => subst hc₀; exact ⟨tp, σ, g, rfl, @Language.NSteps.refl _ _ _ _ gooseRealLang _⟩
  | @cons n c₁ c₂ c₃ κ κs hstep _ ih =>
    subst hc₀
    cases hstep with
    | crash _ hb _ => simp at hb
    | step hstep =>
      cases hstep with
      | @node nodes g i tp₀ σ₀ κ tp₁ σ₁ g₁ hi hs =>
        obtain rfl : i = 0 := by
          have := (List.getElem?_eq_some_iff.mp hi).1
          simp only [List.length_singleton] at this
          omega
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        obtain ⟨tp', σ', g', rfl, hrest⟩ := ih (tp := tp₁) (σ := σ₁) (g := g₁) rfl
        exact ⟨tp', σ', g', rfl, @Language.NSteps.cons _ _ _ _ gooseRealLang _ _ _ _ _ _ hs hrest⟩

/-- **A single process that never crashes**: the conclusion of the single-node adequacy theorem
(`goose_adequacy`: no thread stuck, none with an unrecovered panic, in every real execution of the
program of fewer than `bound` steps) is the robustness statement of the program alone on a
machine that does not crash, a fresh Go process (`Fresh`). -/
theorem Robust.of_single [lctx : GoLocalContext] {e : Expr} {σ : state} {g : GlobalState}
    {bound : Nat}
    (h : Fresh lctx σ →
      ∀ (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState), n < bound →
      RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2) →
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧ (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)) :
    Robust [] [(e, σ)] g bound := by
  intro hfresh n κs c hsteps hn i tp' σ' hi e' he'
  obtain ⟨tp₁, σ₁, g₁, rfl, hreal⟩ := distCrashNsteps_single (tp := [e]) hsteps
  obtain ⟨hns, hnp⟩ := h (hfresh (e, σ) (by simp)) n κs tp₁ (σ₁, g₁) hn hreal
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
