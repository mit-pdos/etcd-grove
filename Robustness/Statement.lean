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

/-- **A robustness statement** (see the file header): in every execution of fewer than `bound`
steps of the machines `crashing` (which may crash and restart) and `stable` (which never crash),
each running its program from its local state, on the shared state `g`, no thread of any machine
is stuck or has an unrecovered panic. -/
def Robust (crashing stable : List (Expr × state)) (g : GlobalState) (bound : Nat) : Prop :=
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
theorem Robust.of_all_crashing {crashing stable : List (Expr × state)} {g : GlobalState}
    {bound : Nat} (h : Robust (crashing ++ stable) [] g bound) : Robust crashing stable g bound := by
  intro n κs c hsteps hn
  refine h n κs c ?_ hn
  rw [List.map_append, List.append_nil]
  exact distCrashNsteps_more_boots _ hsteps

end facts

end Robustness
end Perennial
