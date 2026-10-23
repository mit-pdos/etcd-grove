/- Lean-first (no Rocq counterpart).

# Adequacy of the porcupine counter example (2026-10-19)

A closed theorem about the operational semantics of `Main()`
(`examples/lintest/counter/counter.go`), with no Iris in its statement: the program
`initialize'(); Main()` -- the counter package's initialization (which initializes its
dependencies, porcupine and `context` among them, then the package) followed by `Main` --
started from a fresh state (no package initialized, one thread), for every real execution of
fewer than `2^63` steps, never gets stuck, no thread of it ends in a panic, and the main
thread's result, if it has one, is `#()`.

`Main` runs `Check(lintest.CounterClock(), 4, 10, 0)` -- 4 goroutines of 10 operations each
of a counter under a mutex, traced with a counter clock, the trace checked by porcupine's
translated `CheckOperationsVerbose` with no timeout -- and panics unless the answer is `Ok`.
So no panic means porcupine answered `Ok`.

It follows from Perennial's `goose_adequacy` (through `examples/common/Adequacy.lean`'s `init_adequate`), as the register's (`register/Adequacy.lean`):
the disk FFI (the proofs are generic over the FFI), a concrete ghost-state bundle `counterGF`,
the bounds `N = n + 1` (time receipts) and `T = n + 2` (threads, `Proof/runtime/Threads.lean`),
the package initialization (`counter/Init.lean`, at the program's table `PkgTable.lean`, both
generated; `context`'s `isClosedchanInit`, which `Main.spec` takes, from `context`'s `isPkgInit`,
`context.isClosedchanInit_of_init`) and `counter.wp_Main` (`Link.lean`).

- **The length bound.** `CounterClock`'s spec takes `receiptBound GF ≤ 2^63` (time receipts
  bound the `atomic.Int64` the clock increments, so it does not wrap), and `goose_adequacy`'s
  receipt bound `N` must exceed the execution's length `n`: `N = n + 1 ≤ 2^63`, so the theorem
  is about executions of `n < 2^63` steps.
- **Non-atomic invariants.** Porcupine's `checkSingle` shares the model's state values in
  iris-lean's non-atomic invariants (`porcupine/Shared.lean`), whose camera (`NaInvF`) is not in
  Perennial's `allG`; the porcupine results take `[NaInvG GF]`. Here `counterGF` has a slot for
  it (11), so the instance is concrete and this theorem assumes none.
- **The Go semantics** is a parameter, as in every Perennial result: `GoGlobalContext`,
  `GoLocalContext`, `go.Semantics`, the package assumptions `counter.Assumptions` (every name's
  translated body or Perennial's trusted model, the struct layouts, recursively for the
  imports), and `context`'s two method-set facts (`ErrorStringIsError`,
  `DeadlineExceededIsError`), which its initialization needs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.PkgTable
public import Proof.runtime.Threads
public import Perennial.GooseLang.Ffi.DiskFfi.Adequacy

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace counter

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The ghost-state bundle -/

attribute [local instance] disk_op disk_model disk_semantics disk_interp

/-- The functors: the register's (`registerGF`: the universal camera `AllG` at slot 0, then
invariants, later credits, GooseLang's heap, prophecies and package state, and the disk FFI's
heap), and iris-lean's non-atomic invariants at slot 11. Every other slot is the unit
functor. -/
def counterGF : BundledGFunctors := fun i =>
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
  | 8 => ⟨constOF (HeapView Int (Agree (DiscreteO Block)) (GMap Int)), inferInstance⟩
  | 9 => ⟨constOF (HeapView Int (Agree (DiscreteO GName)) (GMap Int)), inferInstance⟩
  | 10 => ⟨constOF MetaUR, inferInstance⟩
  | 11 => ⟨NaInvF, inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- The universal camera at slot 0 (not an instance: under a `HeapGS` the `AllG` is the one
it carries). -/
def counterGF_allG : AllG counterGF := ⟨⟨0, rfl⟩⟩

instance counterGF_gooseGpreS : GooseGpreS disk_model counterGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGFfi := (⟨⟨⟨⟨8, rfl⟩⟩, ⟨⟨9, rfl⟩⟩, ⟨10, rfl⟩⟩⟩ : DiskPreG counterGF)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := counterGF_allG

/-- iris-lean's camera of non-atomic invariants, at slot 11: the instance the porcupine
results take. -/
instance counterGF_naInvG : NaInvG counterGF := ⟨⟨11, rfl⟩⟩


/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- The counter's program: the package's initialization, then `Main()`. -/
def counterProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.lintest.counter.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.lintest.counter.Main) #()

/-- **Porcupine accepts every trace of the linearizable counter.** Every real execution of
`counterProgram` (the counter package's initialization, then `Main()`) from a fresh state --
no package initialized (`IsInit`), one live thread -- of `n < 2^63` steps: if the main thread
has finished, its result is `#()`; no thread is stuck (each is a value or can step); no thread
has ended in a panic.

What it says about porcupine: `Main` runs 4 clients of 10 operations each (increments for the
even clients, reads for the odd ones) of a counter under a mutex, records each operation's
call and return times with a counter clock, and passes the trace to porcupine's
`CheckOperationsVerbose` (its translated Go code, no timeout), panicking unless the answer is
`Ok`. So for every interleaving of the 4 clients and every choice of the scheduler, porcupine
returned `Ok` on the recorded trace: a non-`Ok` answer would have made `Main` panic.

Parametric in the Go semantics: any `go.Semantics` at the state's local context, any package
assumptions (the translated bodies behind the counter's and its imports' names) and
`context`'s method-set facts. No instance is assumed for the ghost state: the bundle
`counterGF` provides iris-lean's non-atomic invariants (`NaInvG`). -/
theorem counter_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]
    [hErr : context.ErrorStringIsError] [hDE : context.DeadlineExceededIsError]
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (n : Nat) (Hn : n < 2 ^ 63) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([counterProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  refine init_adequate (GF := counterGF) github_com.mit_pdos.etcd_grove.examples.lintest.counter.initialize' ((@! github_com.mit_pdos.etcd_grove.examples.lintest.counter.Main) #())
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) σ g trivial trivial Hlctx Hinit
    Hthreads n κs t2 σ2 Hsteps fun hG HN _ => ?_
  letI : HeapGS .hasLC counterGF := heapWith hG lctx
  have Hbound : receiptBound counterGF ≤ 2 ^ 63 := by rw [HN]; omega
  unfold progOk0
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.lintest.counter.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.lintest.counter.getIsPkgInit_wf, ?_⟩
  iintro #Hpkg -
  ihave #Hcc : context.isClosedchanInit (GF := counterGF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_apply (counter.wp_Main Hbound) $$ [Hpkg Hcc]
  · iframe #
  ipureintro
  rfl

end adequacy

end counter
end lintest
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.lintest.counter.counter_adequate
