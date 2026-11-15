/-
The statement of a robustness theorem [Trusted definitions!], over the executions of Perennial's
distributed semantics (`Perennial/GooseLang/DistLang.lean`), with no semantics of its own.

**The system and its environment are nodes of one distributed system**: the system's nodes `sys`,
which the theorem is about (each its program, run at the start and after every crash, and its
initial local state), then the environment's nodes `env` (any programs: clients, other services,
misbehaving hosts; nothing is proved of them), sharing the global state `g` (the network).

**A run** (`IsRun`) is a sequence of configurations in which each is followed by one that
`DistCrashStep` allows: a real step of one thread of one node, or a crash of one node, which
restarts it with its program from a local state its extensions' crash relations allow. That is
the transition relation of the distributed adequacy theorems (`goose_dist_crash_adequacy`), and a
run is an execution `DistCrashNsteps` with its intermediate configurations kept (`IsRun.nsteps`,
`IsRun.of_nsteps`). Everything else is that relation's nondeterminism: the scheduler (a node that
never runs again, or starts late, is one it does not pick), the crashes, and the faults the
extensions' semantics allow (the TCP extension: a direction cut at any read or write, any delay, a
dial failing; a partition is such a run).

**What is observed** is the shared state: the sequence of global states of the run (a node's heap
and files are not observed). An observer of a network reads its events off the changes
(`Stream.lean`).

`Robust sys env g bound Assume Guarantee` says: in every run of `sys ++ env` from `g` of fewer
than `bound` steps, if the environment behaved as `Assume` requires, then every node of the system
is fine at its end (`NodeOk`: none stuck, no unrecovered panic, the conclusion of the adequacy
theorems) and the run's global states satisfy `Guarantee`.

**`Assume` sees only the environment's steps** (`envSteps`): the changes of the shared state by
the steps that leave every node of the system as it was, in order, without their times. So it can
say what the clients may do, and it cannot mention a step the system took: a statement whose
premise the system's own steps could falsify could be vacuous. (A step of a system node that
changes neither its threads nor its local state would count as the environment's; a real step
changes its thread, except an extension's stutter, which changes nothing. `Assume` may still be
unsatisfiable on its own: reading it is part of reviewing a statement.)

**`Guarantee` sees every global state**, in order, the index being the time: e.g. linearizability
of the clients' operations as the network shows them (`Linearizability.lean`, `Stream.lean`).

The step bound is the proofs' (time receipts, as the closed adequacy theorems' `n < 2^61`).

The system's programs are the real programs (Goose translations), with no fault injection. The Go
harness that tests a deployment the same way is `examples/lib/robust` (`notes/robustness.md`).
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

/-- `cs` is a run of nodes with the boot programs `boots`: each configuration is followed by one
that a step or a crash of a node gives (`DistCrashStep`). -/
def IsRun (boots : List Expr) (cs : List DistCfg) : Prop :=
  ∀ j c c', cs[j]? = some c → cs[j + 1]? = some c' → ∃ κ, DistCrashStep boots c κ c'

open scoped Classical in
/-- The changes of the shared state by the steps of the run `cs` that leave its first `k` nodes
as they were, in order. -/
def envSteps (k : Nat) (cs : List DistCfg) : List (GlobalState × GlobalState) :=
  (cs.zip cs.tail).filterMap fun p =>
    if p.2.nodes.take k = p.1.nodes.take k then some (p.1.global, p.2.global) else none

/-- Node `i` of `c` is fine: no thread of it is stuck, and none has a panic that nothing
recovered (the conclusion of the distributed adequacy theorems, `goose_dist_crash_adequacy`). -/
def NodeOk (c : DistCfg) (i : Nat) : Prop :=
  ∀ tp σ, c.nodes[i]? = some (tp, σ) →
    (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧ (∀ e, e ∈ tp → ¬ UnrecoveredPanic e)

/-- **A robustness statement** (see the file header): every run of the system's nodes `sys` with
the environment's nodes `env` from the shared state `g`, of fewer than `bound` steps, in which
the environment's steps satisfy `Assume`, leaves every node of the system fine, and its global
states satisfy `Guarantee`. -/
def Robust (sys env : List (Expr × state)) (g : GlobalState) (bound : Nat)
    (Assume : List (GlobalState × GlobalState) → Prop) (Guarantee : List GlobalState → Prop) :
    Prop :=
  ∀ cs : List DistCfg,
    let run := distInit (sys ++ env) g :: cs
    IsRun ((sys ++ env).map Prod.fst) run → cs.length < bound →
    Assume (envSteps sys.length run) →
    (∀ c, run.getLast? = some c → ∀ i, i < sys.length → NodeOk c i) ∧
      Guarantee (run.map DistCfg.global)

end statement

/-! ## Sanity: the runs are the executions of `DistCrashNsteps` -/

section facts
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

theorem IsRun.tail {boots : List Expr} {c : DistCfg} {cs : List DistCfg}
    (h : IsRun boots (c :: cs)) : IsRun boots cs :=
  fun j c₁ c₂ h₁ h₂ => h (j + 1) c₁ c₂ h₁ h₂

/-- A run of `n` steps is an execution of `n` steps to its last configuration. -/
theorem IsRun.nsteps {boots : List Expr} {c₀ : DistCfg} {cs : List DistCfg}
    (h : IsRun boots (c₀ :: cs)) {c : DistCfg} (hc : (c₀ :: cs).getLast? = some c) :
    ∃ κs, DistCrashNsteps boots cs.length c₀ κs c := by
  induction cs generalizing c₀ with
  | nil =>
    simp only [List.getLast?_singleton, Option.some.injEq] at hc
    subst hc
    exact ⟨[], .refl _⟩
  | cons c₁ cs ih =>
    obtain ⟨κ, hstep⟩ := h 0 c₀ c₁ rfl rfl
    rw [List.getLast?_cons_cons] at hc
    obtain ⟨κs, hrest⟩ := ih h.tail hc
    exact ⟨κ ++ κs, .cons hstep hrest⟩

/-- An execution of `n` steps is a run of `n` steps with the same last configuration. -/
theorem IsRun.of_nsteps {boots : List Expr} {n : Nat} {c₀ c : DistCfg} {κs : List Observation}
    (h : DistCrashNsteps boots n c₀ κs c) :
    ∃ cs, IsRun boots (c₀ :: cs) ∧ cs.length = n ∧ (c₀ :: cs).getLast? = some c := by
  induction h with
  | refl c => exact ⟨[], fun j _ _ _ h₂ => by simp at h₂, rfl, rfl⟩
  | @cons n c₁ c₂ c₃ κ κs hstep _ ih =>
    obtain ⟨cs, hrun, hlen, hlast⟩ := ih
    refine ⟨c₂ :: cs, ?_, by simp [hlen], by rw [List.getLast?_cons_cons]; exact hlast⟩
    intro j a b ha hb
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at ha hb
      subst ha hb
      exact ⟨κ, hstep⟩
    | succ j => exact hrun j a b ha hb

end facts

end Robustness
end Perennial
