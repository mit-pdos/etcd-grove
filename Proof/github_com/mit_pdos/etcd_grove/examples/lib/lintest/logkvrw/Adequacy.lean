/- Lean-first (no Rocq counterpart).

# Adequacy of the log-applied register example (2026-10-28)

A closed theorem about the operational semantics of `Main()`
(`examples/lib/lintest/logkvrw/logkvrw.go`), with no Iris in its statement: the program
`initialize'(); Main()` -- the logkvrw package's initialization (which initializes its
dependencies, porcupine and `context` among them, then the package) followed by `Main` --
started from a fresh state (no package initialized, one thread), for every real execution of
fewer than `2^30 - 1` steps, never gets stuck, no thread of it ends in a panic, and the main
thread's result, if it has one, is `#()`.

`Main` runs `Check(lintest.CounterClock(), clients, ops, 0)` -- between 1 and 8 goroutines (a
random number) of between 1 and 32 random operations each of a register whose writes go through a log that an apply goroutine applies (a write returns
once applied, a read reads the applied state), traced with a counter clock, the trace checked by porcupine's
translated `CheckOperationsVerbose` with no timeout -- and panics unless the answer is `Ok`.
So no panic means porcupine answered `Ok`.

It follows from Perennial's `goose_adequacy` (through `examples/lib/etcdstart/Adequacy.lean`'s `init_adequate`), as the counter's (`counter/Adequacy.lean`):
no extension (`Robustness.noExts`, `Robustness/NoExts.lean`; the proofs are generic over the
extensions), a concrete ghost-state bundle `logkvrwGF`,
the bounds `N = n + 1` (time receipts) and `T = n + 2` (threads, `Proof/runtime/Threads.lean`),
the package initialization (`logkvrw/Init.lean`, at the program's table `PkgTable.lean`, both
generated; `context`'s `isClosedchanInit`, which `Main.spec` takes, from `context`'s `isPkgInit`,
`context.isClosedchanInit_of_init`) and `logkvrw.wp_Main` (`Link.lean`).

- **The length bound.** `CounterClock`'s spec takes `receiptBound GF ≤ 2^63` (time receipts
  bound the `atomic.Int64` the clock increments, so it does not wrap), and `goose_adequacy`'s
  receipt bound `N` must exceed the execution's length `n`: `N = n + 1 ≤ 2^63`. `New`'s spec
  takes `threadBound GF ≤ 2^30` (the server's `RWMutex` admits `2^30 - 1` readers at once; its
  reader tokens are lent to live threads), and the thread bound is `T = n + 2` (an execution of
  `n` steps has fewer than `n + 2` live threads): `n + 2 ≤ 2^30`, so the theorem is about
  executions of `n < 2^30 - 1` steps (the base's: `n < 2^63`). `logkvrw_adequate_below` takes the
  thread bound from the execution instead (`init_adequate_below`: fewer than `T ≤ 2^30` threads live
  along it), and so holds for every `n < 2^63`; `logkvrw_adequate` is its instance at `T = n + 2`.
- **Non-atomic invariants.** Porcupine's `checkSingle` shares the model's state values in
  iris-lean's non-atomic invariants (`porcupine/Shared.lean`), whose camera (`NaInvF`) is not in
  Perennial's `allG`; the porcupine results take `[NaInvG GF]`. Here `logkvrwGF` has a slot for
  it (11), so the instance is concrete and this theorem assumes none.
- **The Go semantics** is a parameter, as in every Perennial result: `GoGlobalContext`,
  `GoLocalContext`, `go.Semantics`, the package assumptions `logkvrw.Assumptions` (every name's
  translated body or Perennial's trusted model, the struct layouts, recursively for the
  imports), and `context`'s two method-set facts (`ErrorStringIsError`,
  `DeadlineExceededIsError`), which its initialization needs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.PkgTable
public import Proof.runtime.Threads
public import Robustness.Statement
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.TopLevelDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvrw

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The ghost-state bundle -/

attribute [local instance] Robustness.noExts Robustness.noExtsSemantics Robustness.noExtsInterp

/-- The functors: the register's (`registerGF`: the universal camera `AllG` at slot 0, then
invariants, later credits, GooseLang's heap, prophecies and package state), and iris-lean's non-atomic invariants at slot 11. Every other slot is the unit
functor. -/
def logkvrwGF : BundledGFunctors := fun i =>
  match i with
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)),
          inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | 11 => ⟨NaInvF, inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- The universal camera at slot 0 (not an instance: under a `HeapGS` the `AllG` is the one
it carries). -/
def logkvrwGF_allG : AllG logkvrwGF := ⟨⟨0, rfl⟩⟩

instance logkvrwGF_gooseGpreS : GooseGpreS logkvrwGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := PUnit.unit
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := logkvrwGF_allG

/-- iris-lean's camera of non-atomic invariants, at slot 11: the instance the porcupine
results take. -/
instance logkvrwGF_naInvG : NaInvG logkvrwGF := ⟨⟨11, rfl⟩⟩


/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- **`logkvrw_adequate` along executions with fewer than `T ≤ 2^30` live threads**: the same
conclusion for every execution of `n < 2^63` steps along which fewer than `T` threads are ever
live at once (`RealNstepsBelow`): the thread bound is a premise on the execution, not a
consequence of its length. -/
theorem logkvrw_adequate_below [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.Assumptions]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (T : Nat) (HT : T ≤ 2 ^ 30)
    (n : Nat) (Hn : n < 2 ^ 63) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow T n ([logkvrwProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine init_adequate_below (GF := logkvrwGF) github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.initialize' ((@! github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.Main) #())
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) σ g trivial trivial Hlctx Hinit
    Hthreads T n κs t2 σ2 Hsteps fun hG HN HT' => ?_
  letI : HeapGS .hasLC logkvrwGF := heapWith hG lctx
  have Hbound : receiptBound logkvrwGF ≤ 2 ^ 63 := by rw [HN]; omega
  have Htb : threadBound logkvrwGF ≤ 2 ^ 30 := by rw [HT']; omega
  unfold progOk0
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.getIsPkgInit_wf, ?_⟩
  iintro #Hpkg -
  ihave #Hcc : context.isClosedchanInit (GF := logkvrwGF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_apply (logkvrw.wp_Main Hbound Htb) $$ [Hpkg Hcc]
  · iframe #
  ipureintro
  rfl

/-- **Porcupine accepts every trace of the log-applied register.** Every real execution of
`logkvrwProgram` (the logkvrw package's initialization, then `Main()`) from a fresh state --
no package initialized (`IsInit`), one live thread -- of `n < 2^30 - 1` steps: if the main thread
has finished, its result is `#()`; no thread is stuck (each is a value or can step); no thread
has ended in a panic.

What it says about porcupine: `Main` runs a random number (1 to 8) of clients of a random number (1 to 32) of
operations each (each at random a write of one of eight values or a read) of the log-applied register, records each operation's
call and return times with a counter clock, and passes the trace to porcupine's
`CheckOperationsVerbose` (its translated Go code, no timeout), panicking unless the answer is
`Ok`. So for every draw of the random numbers, every interleaving of the clients and every choice of
the scheduler, porcupine
returned `Ok` on the recorded trace: a non-`Ok` answer would have made `Main` panic.

Parametric in the Go semantics: any `go.Semantics` at the state's local context, any package
assumptions (the translated bodies behind the logkvrw package's and its imports' names) and
`context`'s method-set facts. No instance is assumed for the ghost state: the bundle
`logkvrwGF` provides iris-lean's non-atomic invariants (`NaInvG`). -/
theorem logkvrw_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.Assumptions]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n < 2 ^ 30 - 1) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([logkvrwProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  logkvrw_adequate_below σ g Hlctx Hinit Hthreads (n + 2) (by omega) n (by omega) κs t2 σ2
    (RealNstepsBelow.of_one Hsteps Hthreads)

end adequacy

end logkvrw
end lintest
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.lintest.logkvrw.logkvrw_adequate
#print axioms Perennial.EtcdGrove.lintest.logkvrw.logkvrw_adequate_below
