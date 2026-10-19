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

It follows from Perennial's `goose_adequacy`, as the register's (`register/Adequacy.lean`):
the disk FFI (the proofs are generic over the FFI), a concrete ghost-state bundle `counterGF`,
the bounds `N = n + 1` (time receipts) and `T = n + 2` (threads, `Proof/runtime/Threads.lean`),
the package initialization (`counter/Init.lean`, which also gives `context`'s
`isClosedchanInit`) and `counter.wp_Main` (`Link.lean`).

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

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Init
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

/-! ## Package initialization's starting point -/

section pkgs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]

/-- The post-initialization predicate of every package the counter (transitively) imports,
and of the counter itself: what `ownInitializing` hands out for an initialized package. The
entries of `context` and of the packages that import it (porcupine, lintest, the counter)
also carry `context.isClosedchanInit` (`porcupine/Init.lean`). -/
def pkgInitTable : List (GoString × IProp GF) :=
  [(pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.counter,
      iprop(isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.counter ∗
        context.isClosedchanInit)),
   (pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest,
      iprop(isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest ∗
        context.isClosedchanInit)),
   (pkg_id.github_com.anishathalye.porcupine,
      iprop(isPkgInit pkg_id.github_com.anishathalye.porcupine ∗ context.isClosedchanInit)),
   (pkg_id.context, iprop(isPkgInit pkg_id.context ∗ context.isClosedchanInit)),
   (pkg_id.sort, isPkgInit pkg_id.sort),
   (pkg_id.math.bits, isPkgInit pkg_id.math.bits),
   (pkg_id.«unsafe», isPkgInit pkg_id.«unsafe»),
   (pkg_id.time, isPkgInit pkg_id.time),
   (pkg_id.fmt, isPkgInit pkg_id.fmt),
   (pkg_id.io, isPkgInit pkg_id.io),
   (pkg_id.errors, isPkgInit pkg_id.errors),
   (pkg_id.sync, isPkgInit pkg_id.sync),
   (pkg_id.sync.atomic, isPkgInit pkg_id.sync.atomic),
   (pkg_id.internal.race, isPkgInit pkg_id.internal.race),
   (pkg_id.internal.synctest, isPkgInit pkg_id.internal.synctest),
   (pkg_id.strings, isPkgInit pkg_id.strings)]

/-- `get_is_pkg_init` for the counter's program: a package's entry in `pkgInitTable`. -/
def getIsPkgInit (s : GoString) : IProp GF :=
  ((pkgInitTable (GF := GF)).lookup s).getD iprop(True)

theorem getIsPkgInit_porcupine :
    github_com.anishathalye.porcupine.PorcupineInitTable (getIsPkgInit (GF := GF)) where
  self := rfl
  context := rfl
  errors := by repeat' (first | exact True.intro | apply And.intro | rfl)
  sync := by repeat' (first | exact True.intro | apply And.intro | rfl)
  atomic := by repeat' (first | exact True.intro | apply And.intro | rfl)
  time := by repeat' (first | exact True.intro | apply And.intro | rfl)
  sort := by repeat' (first | exact True.intro | apply And.intro | rfl)
  fmt := by repeat' (first | exact True.intro | apply And.intro | rfl)
  strings := by repeat' (first | exact True.intro | apply And.intro | rfl)

end pkgs

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
  suffices H : (∀ v t2', t2 = Val v :: t2' → v = #()) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) by
    refine ⟨H.1, H.2.1, fun v hv => ?_⟩
    cases h : v.isPanic
    · rfl
    · obtain ⟨p, rfl⟩ := val.isPanic_eq_true h
      exact absurd (UnrecoveredPanic.panic p) (H.2.2 _ hv)
  refine goose_adequacy (GF := counterGF) (n + 1) (n + 2) counterProgram σ g
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) trivial trivial ?_
    n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads (realThreadsBelow_of_one Hthreads)
  intro hG HN _ HL
  obtain ⟨G, ⟨fl, lc, nh, gs⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC counterGF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs⟩⟩
  have Hbound : receiptBound counterGF ≤ 2 ^ 63 := by rw [HN]; omega
  unfold IsInit at Hinit
  rw [Hinit]
  iintro _ _ Hgs Htok
  ihave Hown : ownInitializing (getIsPkgInit (GF := counterGF)) $$ [Hgs]
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    imodintro
    iapply BigSepM.bigSepM_empty.2
    itrivial
  imodintro
  unfold counterProgram
  wp_apply (github_com.mit_pdos.etcd_grove.examples.lintest.counter.wp_initialize' _
    getIsPkgInit_porcupine rfl rfl) $$ Hown as ⟨_, #Hpkg, #Hcc⟩
  wp_apply counter.wp_Main Hbound $$ [Hpkg Hcc]
  · iframe #
  ipureintro
  rfl

end adequacy

end counter
end lintest
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.lintest.counter.counter_adequate
