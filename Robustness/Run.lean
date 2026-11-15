/-
Runs of a deployed system in its environment [Trusted definitions!]: what a robustness theorem
quantifies over (`Statement.lean`).

A run is an execution of Perennial's distributed semantics (`DistLang.lean`: nodes, each a thread
pool and a local state, sharing a global state) in which every step is one of

* a real step of one thread of one node (`DistStep`'s, any node: the system's or the
  environment's, the scheduler being the environment);
* a crash of one node (`DistCrashStep`'s): all its threads die, its local state becomes one that
  the extensions' crash relations allow (for a file system, what survives a power loss), and it
  starts again running its boot program alone. The node's process killed and its file system
  synced before the restart is such a crash too, under the Linux file extension's "Restarts"
  assumption (`GooseLang/Ext/Fs/Impl.lean`); a node that never runs again is one the scheduler
  never picks; a node started late is one the scheduler does not pick before;
* a move of the world (`World.move`): a change of the global state that no node makes (for a
  network that does not itself allow a fault, an operator's partition, say). For a network whose
  semantics already allows every fault at every step (the TCP extension: a direction may break at
  any read or write, and any delay is a schedule), `World.move` is empty.

What the run shows an outside observer is a trace of events (`Timed`), each the change of the
global state by a step, as the world's observation function reads it (`World.obs`, e.g. the bytes
appended to a connection), stamped with the step's index (the real-time order: the run's
interleaving is the order in which things happen) and with who made the step (`Who`). A node's
local state (its heap, its files) is not observed: only what crosses the shared state.

`NodeOk c i` is what the adequacy theorems say of a node: no thread of node `i` is stuck, and no
thread has a panic that nothing recovered.
-/
module

public import Perennial.GooseLang.DistLang

@[expose] public section

noncomputable section

namespace Perennial
namespace Robustness

open Iris.ProgramLogic

/-- Who takes a step of a run: node `i` (a step of one of its threads, or its crash), or the
world (a move of the environment on the shared state). -/
inductive Who where
  | node (i : Nat)
  | world
deriving DecidableEq

/-- An event an outside observer sees, at the index `time` of the step that made it, by `who`. -/
structure Timed (Ev : Type) where
  time : Nat
  who : Who
  ev : Ev

section run
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- The world a system runs in, beyond the semantics of its nodes: the moves of the environment on
the shared state that no node makes, and what an outside observer sees of a change of the shared
state (`obs g g'`: the events of a step from `g` to `g'`, oldest first). -/
structure World (Ev : Type) where
  move : GlobalState → GlobalState → Prop
  obs : GlobalState → GlobalState → List Ev

variable {Ev : Type}

/-- A step of a run of nodes with the boot programs `boots`, in the world `W`, by `who`. -/
inductive RunStep (W : World Ev) (boots : List Expr) : DistCfg → Who → DistCfg → Prop
  /-- a real step of a thread of node `i` -/
  | node {nodes : List (List Expr × state)} {g : GlobalState} {i : Nat} {tp : List Expr}
      {σ : state} {κ : List Observation} {tp' : List Expr} {σ' : state} {g' : GlobalState} :
      nodes[i]? = some (tp, σ) →
      @Language.Step _ _ _ _ gooseRealLang (tp, (σ, g)) κ (tp', (σ', g')) →
      RunStep W boots ⟨nodes, g⟩ (.node i) ⟨nodes.set i (tp', σ'), g'⟩
  /-- a crash of node `i`, which restarts it with its boot program alone, from a local state the
  crash relation allows; the shared state is unchanged -/
  | crash {nodes : List (List Expr × state)} {g : GlobalState} {i : Nat} {tp : List Expr}
      {σ : state} {e : Expr} {σ' : state} :
      nodes[i]? = some (tp, σ) → boots[i]? = some e → Crash σ σ' →
      RunStep W boots ⟨nodes, g⟩ (.node i) ⟨nodes.set i ([e], σ'), g⟩
  /-- a move of the world -/
  | world {nodes : List (List Expr × state)} {g g' : GlobalState} :
      W.move g g' → RunStep W boots ⟨nodes, g⟩ .world ⟨nodes, g'⟩

/-- A run of `n` steps from `c₀` to `c`, with the trace `tr` of the events its steps made, in
order: step `k` (from `0`) from `c` to `c'` by `w` adds `W.obs c.global c'.global`, each stamped
`k` and `w`. -/
inductive Run (W : World Ev) (boots : List Expr) (c₀ : DistCfg) :
    Nat → List (Timed Ev) → DistCfg → Prop
  | nil : Run W boots c₀ 0 [] c₀
  | snoc {n : Nat} {tr : List (Timed Ev)} {c c' : DistCfg} {w : Who} :
      Run W boots c₀ n tr c → RunStep W boots c w c' →
      Run W boots c₀ (n + 1) (tr ++ (W.obs c.global c'.global).map (fun e => ⟨n, w, e⟩)) c'

/-- Node `i` of `c` is fine: no thread of it is stuck, and none has a panic that nothing
recovered (the conclusion of the distributed adequacy theorems, `goose_dist_crash_adequacy`). -/
def NodeOk (c : DistCfg) (i : Nat) : Prop :=
  ∀ tp σ, c.nodes[i]? = some (tp, σ) →
    (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧ (∀ e, e ∈ tp → ¬ UnrecoveredPanic e)

end run

/-! ## Sanity: runs extend -/

section facts
variable [GooseExts] [GooseSemantics] [GoGlobalContext] {Ev : Type}

/-- A run's trace only grows: a later step does not change the events of the earlier ones. -/
theorem Run.snoc_prefix {W : World Ev} {boots : List Expr} {c₀ c c' : DistCfg} {n : Nat}
    {tr : List (Timed Ev)} {w : Who} (h : Run W boots c₀ n tr c) (hs : RunStep W boots c w c') :
    ∃ tr', Run W boots c₀ (n + 1) (tr ++ tr') c' :=
  ⟨_, .snoc h hs⟩

/-- Every event of a run's trace is stamped with the index of a step of the run. -/
theorem Run.time_lt {W : World Ev} {boots : List Expr} {c₀ c : DistCfg} {n : Nat}
    {tr : List (Timed Ev)} (h : Run W boots c₀ n tr c) : ∀ x ∈ tr, x.time < n := by
  induction h with
  | nil => simp
  | snoc _ _ ih =>
    intro x hx
    simp only [List.mem_append, List.mem_map] at hx
    rcases hx with hx | ⟨e, _, rfl⟩
    · have := ih x hx; omega
    · simp

end facts

end Robustness
end Perennial
