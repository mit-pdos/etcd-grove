/- Lean-first (no Rocq counterpart).

# Adequacy of the trace check (S7 (part 1), 2026-11-11)

The closed theorem's shape (`notes/trace-validation-plan.md`, "The statement"; as
`raft_kv_porcupine_safe`'s, `kv/Adequacy.lean`): the program `initialize'(); Main()` -- the
tracecheck package's initialization (raft's, the checker's, `context`'s and the others' among its
imports'), then `Main` -- from a fresh state (no package initialized, one thread), for every real
execution of `n` steps with `n + 4 ≤ 2^61` along which fewer than `2^31` threads are ever live at once
(`RealNstepsBelow`; 2026-11-19, replacing Q38's `n + 2 ≤ 2^31`), never gets stuck, no thread of it ends in a panic, and
the main thread's result, if it has one, is `#()`. `Main` panics unless `CheckTrace` answers `TLCOK`
on the run's trace, so no panic means the trace passes raft's TLA+ trace validation.

From Perennial's `goose_adequacy_below` through `examples/lib/etcdstart/Adequacy.lean`'s `init_adequate_below`,
as the store's (`kv/Adequacy.lean`): the trivial extension, a ghost-state bundle `tcGF` (the store's
without iris-lean's non-atomic invariants, which nothing here uses), the receipt bound `N = n + 1`, the
package initialization (`Init.lean`, `PkgTable.lean`, generated) and `Main`'s spec as a hypothesis
(`tracecheck_adequate_of`).

- **The length bound** (Q38 (a), decided by the user, 2026-11-11). `Main.spec` takes
  `receiptBound GF + 3 ≤ 2^61`: the traced cluster boots three voters from a bootstrap log of three
  entries, and raft's `readyFits` (`cluster_alloc`'s premise) is `receiptBound + bootLen ≤ 2^61`; the
  same bound gives the event count below the checker's `numBound = 2^61`. It also takes the thread
  bound `[ThreadBoundLe GF (2 ^ 31)]`: the harness starts a goroutine per message and counts them in a
  `sync.WaitGroup`, which panics past `2^31` (`NetJoin.lean`). With `N = n + 1` and `T = 2^31` (the
  execution's own thread bound, `RealNstepsBelow (2^31) n`), the theorem is about executions of
  `n + 4 ≤ 2^61` steps (`receiptBound + 3 = n + 4`) in which fewer than `2^31` goroutines are live at
  once. (Until 2026-11-19, `T = n + 2` over `goose_adequacy`, whose thread premise is about every
  execution of `n` steps, so `n + 2 ≤ 2^31`: the step count was capped by the thread bound.)
- **The premises** (Q32, decided by the user): the bootstrap log's pure facts
  (`tracecheck.BootLogFacts`) and, at every `HeapGS`, `proto.Marshal`'s contract at its conf changes
  (`tracecheck.premises`, `Defs.lean`), as `etcd_putget_adequate`.
- **The Go semantics** is a parameter, as in every Perennial result: `GoGlobalContext`,
  `GoLocalContext`, `go.Semantics`, the package assumptions `tracecheck.Assumptions`, and raft's
  initialization premise, the model of `log.New` (`log.NewModel`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Adequacy
public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Init
public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.PkgTable
public import RaftTla.Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Main
public import Proof.runtime.Threads
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt
public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Defs
public import RaftTla.Proof.google_golang_org.protobuf.proto.MarshalBootConfChange
public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.TopLevelDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The ghost-state bundle -/

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

/-- The universal camera at slot 0. -/
@[instance_reducible] def tcGF_allG : AllG tcGF := ⟨⟨0, rfl⟩⟩

instance tcGF_gooseGpreS : GooseGpreS tcGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨tcGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := tcGF_allG

/-! ## The closed theorem, from `Main`'s spec -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- `Main`'s spec at `tcGF`, for every `HeapGS` (hence every local context), every semantics and
every package assumptions (with, inside `Main.spec`, the thread bound, the receipt bound and the
premises): the hypothesis of `tracecheck_adequate_of`. -/
abbrev tcMainSpec : Prop :=
  ∀ [hG : HeapGS HasLC.hasLC tcGF] [go.Semantics]
    [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions],
    TraceCheck.Main.spec (GF := tcGF) (hG := hG)

/-- **The trace check never fails**, from `Main`'s spec (at every `HeapGS` of `tcGF` and every
semantics): every real execution of `tracecheckProgram` (the package's initialization, then
`Main()`) from a fresh state -- no package initialized (`IsInit`), one live thread -- of `n` steps,
`n + 4 ≤ 2^61`, along which fewer than `2^31` threads are live at once, given the bootstrap log's facts and premises: if the main thread has finished, its
result is `#()`; no thread is stuck; no thread has ended in a panic. -/
theorem tracecheck_adequate_of [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]
    [hLog : log.NewModel]
    (wp_Main : tcMainSpec)
    (boot : List LogEntry) (Hbf : tracecheck.BootLogFacts boot) (Hbw : tracecheck.BootWireFacts boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (Hn : n + 4 ≤ 2 ^ 61) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow (2 ^ 31) n ([tracecheckProgram], ((σ, g) : CfgState)) κs (t2, σ2)) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine init_adequate_below (GF := tcGF) github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.initialize'
    ((@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Main) #())
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) σ g ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ Hlctx Hinit
    Hthreads (2 ^ 31) n κs t2 σ2 Hsteps fun hG HN HT => ?_
  letI : HeapGS .hasLC tcGF := heapWith hG lctx
  haveI : ThreadBoundLe tcGF (2 ^ 31) := ⟨Nat.le_of_eq HT⟩
  have Hbound : receiptBound tcGF + 3 ≤ 2 ^ 61 := by rw [HN]; omega
  unfold progOk0
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.getIsPkgInit_wf, ?_⟩
  iintro #Hpkg -
  -- (premises to axioms, 2026-11-24: until then the premise `tracecheck.premises`) `bootMarshal` from
  -- `proto.Marshal`'s trust-boundary axiom and the log's bytes
  ihave #Hpp : isPkgInit (PROP := IProp tcGF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave #Hprem' := tracecheck.premises_of_spec proto.MarshalBootConfChange.wp_proof boot Hbw $$ Hpp
  ihave #Hcc : context.isClosedchanInit (GF := tcGF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_apply (wp_Main (TraceCheck.tcRunFits.intro Hbound) boot Hbf) $$ [Hpkg Hcc Hprem']
  · iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial
