/- Lean-first (no Rocq counterpart).

# Adequacy of the store's linearizability test (2026-10-19)

A closed theorem about the operational semantics of `Main()` (`examples/kv/check.go`), with no
Iris in its statement: the program `initialize'(); Main()` -- the store package's
initialization (which initializes its dependencies, raft, lintest, porcupine and `context`
among them, then the package) followed by `Main` -- started from a fresh state (no package
initialized, one thread), for every real execution of fewer than `2^63` steps, never gets
stuck, no thread of it ends in a panic, and the main thread's result, if it has one, is `#()`.

`Main` starts the 3-node raft cluster (`StartCluster`), runs the randomized linearizability test
`Check(kvs, lintest.CounterClock(), 4, 25)` -- random `Put`/`Get`/`Append` traffic from 4
clients, traced with a counter clock, the trace checked by porcupine's translated checker
against the store's model -- and panics unless the answer is `Ok`. So no panic means porcupine
never rejects the store's trace.

It follows from Perennial's `goose_adequacy` (through `examples/common/Adequacy.lean`'s `init_adequate`), as the register's and the counter's
(`lintest/counter/Adequacy.lean`): the trivial extension (`common/TrivialExt.lean`; the proofs are generic over the extensions), a
concrete ghost-state bundle `kvGF`, the bounds `N = n + 1` (time receipts) and `T = n + 2`
(threads, `Proof/runtime/Threads.lean`), the package initialization (`Init.lean`, at the program's table
`PkgTable.lean`, both generated; `context`'s `isClosedchanInit`, which `Main.spec` takes, from
`context`'s `isPkgInit`, `context.isClosedchanInit_of_init`) and `Main`'s spec. This file proves it from `Main.spec`
as a hypothesis (`kv_adequate_of`); `AdequacyLinked.lean` applies it to the linked result
`kv.wp_Main` (`Link.lean`): `kv_adequate`.

- **The length bound.** `Main.spec` takes `receiptBound GF ≤ 2^63` (the counter clock does not
  wrap; raft's terms stay below `2^64`), and `goose_adequacy`'s receipt bound `N` must exceed
  the execution's length `n`: `N = n + 1 ≤ 2^63`, so the theorem is about executions of
  `n < 2^63` steps.
- **Non-atomic invariants.** Porcupine's results take `[NaInvG GF]` (iris-lean's camera of
  non-atomic invariants, not in Perennial's `allG`); `kvGF` has a slot for it (11), so the
  instance is concrete and the theorem assumes none.
- **The Go semantics** is a parameter, as in every Perennial result: `GoGlobalContext`,
  `GoLocalContext`, `go.Semantics`, the package assumptions `kv.Assumptions` (every name's
  translated body or Perennial's trusted model, the struct layouts, recursively for the
  imports, method sets included), and raft's initialization premise: the model of `log.New`
  (`log.NewModel`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.PkgTable
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Main
public import Proof.runtime.Threads
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.TrivialExt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The ghost-state bundle -/

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

/-- The functors: the universal camera (`AllG`) at slot 0, then invariants, later credits,
GooseLang's heap, prophecies and package state, and
iris-lean's non-atomic invariants at slot 11 (the counter's). Every other slot is the unit
functor. -/
def kvGF : BundledGFunctors := fun i =>
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
it carries, `GooseGlobalGS.gooseAllG`). -/
@[instance_reducible] def kvGF_allG : AllG kvGF := ⟨⟨0, rfl⟩⟩

instance kvGF_gooseGpreS : GooseGpreS kvGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := ((), PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := kvGF_allG

/-- iris-lean's camera of non-atomic invariants, at slot 11: the instance the porcupine
results take. -/
instance kvGF_naInvG : NaInvG kvGF := ⟨⟨11, rfl⟩⟩


/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- `Main`'s spec at `kvGF`, for every `HeapGS` (hence every local context), every semantics
and every package assumptions: what `Main.wp_proof` gives, the hypothesis of
`kv_adequate_of`. -/
abbrev kvMainSpec : Prop :=
  ∀ [hG : HeapGS HasLC.hasLC kvGF] [go.Semantics]
    [github_com.mit_pdos.etcd_grove.examples.kv.Assumptions],
    kv.Main.spec (GF := kvGF) (hG := hG)

/-- The store's program: the package's initialization, then `Main()`. -/
def kvProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.kv.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.kv.Main) #()

/-- **Porcupine never rejects the store's trace**, from `Main`'s spec (`wp_Main`, at every
`HeapGS` of `kvGF` and every semantics): every real execution of `kvProgram` (the store package's initialization,
then `Main()`) from a fresh state -- no package initialized (`IsInit`), one live thread -- of
`n < 2^63` steps: if the main thread has finished, its result is `#()`; no thread is stuck
(each is a value or can step); no thread has ended in a panic. `Main` panics unless porcupine
answers `Ok` on the trace of the randomized test against the 3-node cluster (see the file
header), so porcupine answered `Ok` in every interleaving and every choice of the scheduler.

Parametric in the Go semantics: any `go.Semantics` at the state's local context, any package
assumptions (the translated bodies behind the store's and its imports' names) and the model of
`log.New`. No instance is assumed for the ghost state: the
bundle `kvGF` provides iris-lean's non-atomic invariants (`NaInvG`). -/
theorem kv_adequate_of [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
    [hLog : log.NewModel]
    (wp_Main : kvMainSpec)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n < 2 ^ 63) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  refine init_adequate (GF := kvGF) github_com.mit_pdos.etcd_grove.examples.kv.initialize' ((@! github_com.mit_pdos.etcd_grove.examples.kv.Main) #())
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) σ g ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ Hlctx Hinit
    Hthreads n κs t2 σ2 Hsteps fun hG HN _ => ?_
  letI : HeapGS .hasLC kvGF := heapWith hG lctx
  have Hbound : receiptBound kvGF ≤ 2 ^ 63 := by rw [HN]; omega
  unfold progOk0
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.kv.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.kv.getIsPkgInit_wf, ?_⟩
  iintro #Hpkg -
  ihave #Hcc : context.isClosedchanInit (GF := kvGF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_apply (wp_Main Hbound) $$ [Hpkg Hcc]
  · iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.kv_adequate_of
