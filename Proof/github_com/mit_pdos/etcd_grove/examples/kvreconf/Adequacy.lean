/- Lean-first (no Rocq counterpart).

# Adequacy of the reconfiguring store's linearizability test (2026-10-30, kvreconf-final)

kv's `Adequacy.lean` (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/Adequacy.lean`) for
`examples/kvreconf`: a closed theorem about the operational semantics of `Main()`
(`examples/kvreconf/check.go`), with no Iris in its statement: the program `initialize'(); Main()`
-- the store package's initialization (which initializes its dependencies, raft, lintest,
porcupine and `context` among them, then the package) followed by `Main` -- started from a fresh
state (no package initialized, one thread), for every real execution of fewer than `2^63` steps,
never gets stuck, no thread of it ends in a panic, and the main thread's result, if it has one, is
`#()`.

`Main` starts a cluster of random options (`RandomConfig`: one to five voters, ...), runs the
randomized linearizability test `Run(cfg, lintest.CounterClock())` -- random `Put`/`Get`/`Read`
traffic from 4 clients of 100 operations, traced with a counter clock, while one to three proposers
change the configuration and leadership is disrupted; the trace checked by porcupine's translated
checker against the store's model -- panics unless the answer is `Ok`, then stops the cluster. So
no panic means porcupine never rejects the store's trace.

It follows from Perennial's `goose_adequacy` (through `examples/common/Adequacy.lean`'s
`init_adequate`) as kv's: the trivial extension, a concrete ghost-state bundle `kvrGF` (kv's
`kvGF`: the universal camera `AllG` at slot 0, which holds every ghost map and variable the store's
proofs allocate, the storage registry `KvrStor`'s among them, and iris-lean's non-atomic invariants
`NaInvG` at slot 11, which porcupine's results take), the bounds `N = n + 1` (time receipts) and
`T = n + 2` (threads), the package initialization (`Init.lean`, at the program's table
`PkgTable.lean`, both generated; `context`'s `isClosedchanInit` from `context`'s `isPkgInit`) and
`Main`'s spec. This file proves it from `Main.spec` as a hypothesis (`kvreconf_adequate_of`);
`AdequacyLinked.lean` applies it to the linked result `kvreconf.wp_Main` (`Link.lean`).

- **The length bound.** `Main.spec` takes `receiptBound GF ≤ 2^63` (the counter clock does not
  wrap; raft's step bound `2^64 - 2` holds), and `goose_adequacy`'s receipt bound `N` must exceed
  the execution's length `n`: `N = n + 1 ≤ 2^63`, so the theorem is about executions of
  `n < 2^63` steps.
- **The Go semantics** is a parameter, as in every Perennial result: `GoGlobalContext`,
  `GoLocalContext`, `go.Semantics`, the package assumptions `kvreconf.Assumptions` (every name's
  translated body or Perennial's trusted model, the struct layouts, recursively for the imports,
  raft's among them), and raft's initialization premise: the model of `log.New`
  (`log.NewModel`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.PkgTable
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Main
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

/-- The functors (kv's `kvGF`): the universal camera (`AllG`) at slot 0, then invariants, later
credits, GooseLang's heap, prophecies and package state, and iris-lean's non-atomic invariants at
slot 11. Every other slot is the unit functor. -/
def kvrGF : BundledGFunctors := fun i =>
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
@[instance_reducible] def kvrGF_allG : AllG kvrGF := ⟨⟨0, rfl⟩⟩

instance kvrGF_gooseGpreS : GooseGpreS kvrGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := ((), PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := kvrGF_allG

/-- iris-lean's camera of non-atomic invariants, at slot 11: the instance the porcupine
results take. -/
instance kvrGF_naInvG : NaInvG kvrGF := ⟨⟨11, rfl⟩⟩


/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- `Main`'s spec at `kvrGF`, for every `HeapGS` (hence every local context), every semantics
and every package assumptions: what `Main.wp_proof` gives, the hypothesis of
`kvreconf_adequate_of`. -/
abbrev kvrMainSpec : Prop :=
  ∀ [hG : HeapGS HasLC.hasLC kvrGF] [go.Semantics]
    [github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions],
    kvreconf.Main.spec (GF := kvrGF) (hG := hG)

/-- The store's program: the package's initialization, then `Main()`. -/
def kvreconfProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.kvreconf.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.Main) #()

/-- **Porcupine never rejects the reconfiguring store's trace**, from `Main`'s spec (`wp_Main`, at
every `HeapGS` of `kvrGF` and every semantics): every real execution of `kvreconfProgram` (the
store package's initialization, then `Main()`) from a fresh state -- no package initialized
(`IsInit`), one live thread -- of `n < 2^63` steps: if the main thread has finished, its result is
`#()`; no thread is stuck (each is a value or can step); no thread has ended in a panic. `Main`
panics unless porcupine answers `Ok` on the trace of the randomized test against a cluster of
random options under configuration changes and leadership disruptions (see the file header), so
porcupine answered `Ok` in every interleaving and every choice of the scheduler.

Parametric in the Go semantics: any `go.Semantics` at the state's local context, any package
assumptions (the translated bodies behind the store's and its imports' names) and the model of
`log.New`. No instance is assumed for the ghost state: the bundle `kvrGF` provides iris-lean's
non-atomic invariants (`NaInvG`). -/
theorem kvreconf_adequate_of [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
    [hLog : log.NewModel]
    (wp_Main : kvrMainSpec)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n < 2 ^ 63) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([kvreconfProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  refine init_adequate (GF := kvrGF) github_com.mit_pdos.etcd_grove.examples.kvreconf.initialize'
    ((@! github_com.mit_pdos.etcd_grove.examples.kvreconf.Main) #())
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) σ g ⟨trivial, trivial⟩
    ⟨trivial, trivial⟩ Hlctx Hinit Hthreads n κs t2 σ2 Hsteps fun hG HN _ => ?_
  letI : HeapGS .hasLC kvrGF := heapWith hG lctx
  have Hbound : receiptBound kvrGF ≤ 2 ^ 63 := by rw [HN]; omega
  unfold progOk0
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.kvreconf.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.kvreconf.getIsPkgInit_wf, ?_⟩
  iintro #Hpkg -
  ihave #Hcc : context.isClosedchanInit (GF := kvrGF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_apply (wp_Main Hbound) $$ [Hpkg Hcc]
  · iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.kvreconf_adequate_of
