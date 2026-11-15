/-
The statement of a robustness theorem [Trusted definitions!].

A **deployment** (`Deployment`) is the system's nodes, which the theorem is about (each its
program, run at the start and after every crash, and its initial local state), the environment's
nodes (any programs: clients, other services, misbehaving hosts; nothing is proved of them), and
the shared state at the start.

`Robust W d bound Assume Guarantee` says: in every run of `d` in the world `W` (`Run.lean`:
any interleaving, a crash of any node at any step, any move of the world) of fewer than `bound`
steps, if the environment behaved as `Assume` requires, then every node of the system is fine
(`NodeOk`: none stuck, no unrecovered panic) and the run's trace satisfies `Guarantee`.

**`Assume` sees only the environment.** It is a property of the events the environment's nodes and
the world made, in order (`envEvents`), without their times and without the system's events: what
the clients and the network may do, never a restriction on what the system answers. A statement
whose premise could depend on the system's outputs could be vacuous (the premise false of every
run the system has); this one cannot depend on them. (It may still be unsatisfiable on its own:
reading `Assume` is part of reviewing a statement.)

**`Guarantee` sees everything**, with times: e.g. linearizability of the clients' operations as the
trace shows them (`Linearizability.lean`, `Stream.lean`).

The step bound is the proofs' (time receipts, as the closed adequacy theorems' `n < 2^61`): every
run of a real test is far shorter.

Every fault is the environment's: the system's programs are the real programs (Goose
translations), with no fault injection; the faults are the semantics' nondeterminism (crashes,
the network's), the scheduler's, the world's moves, and the environment's nodes. The Go harness
that tests a deployment the same way is `examples/lib/robust` (`notes/robustness.md`).
-/
module

public import Robustness.Run

@[expose] public section

noncomputable section

namespace Perennial
namespace Robustness

section statement
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- A deployment: the system's nodes (verified: each its boot program and its initial local
state), the environment's nodes (not verified), and the shared state at the start. Node `i` of a
run is `sys[i]` for `i < sys.length`, then the environment's. -/
structure Deployment where
  sys : List (Expr × state)
  env : List (Expr × state)
  global : GlobalState

/-- Every node of `d`: the system's, then the environment's. -/
def Deployment.nodes (d : Deployment) : List (Expr × state) := d.sys ++ d.env

/-- The boot programs of `d`'s nodes, by index. -/
def Deployment.boots (d : Deployment) : List Expr := d.nodes.map Prod.fst

/-- The configuration `d` starts in: each node running its program alone. -/
def Deployment.init (d : Deployment) : DistCfg := distInit d.nodes d.global

/-- A step by `w` is the environment's: a step or crash of one of its nodes, or a world move. -/
def Deployment.byEnv (d : Deployment) : Who → Bool
  | .node i => d.sys.length ≤ i
  | .world => true

variable {Ev : Type}

/-- The events of the trace `tr` the environment made, in order, without times. -/
def Deployment.envEvents (d : Deployment) (tr : List (Timed Ev)) : List Ev :=
  (tr.filter fun x => d.byEnv x.who).map Timed.ev

/-- **A robustness statement**: every run of `d` in the world `W` of fewer than `bound` steps in
which the environment's events satisfy `Assume` leaves every node of the system fine and has a
trace that satisfies `Guarantee` (see the file header). -/
def Robust (W : World Ev) (d : Deployment) (bound : Nat) (Assume : List Ev → Prop)
    (Guarantee : List (Timed Ev) → Prop) : Prop :=
  ∀ n tr c, Run W d.boots d.init n tr c → n < bound → Assume (d.envEvents tr) →
    (∀ i, i < d.sys.length → NodeOk c i) ∧ Guarantee tr

end statement

end Robustness
end Perennial
