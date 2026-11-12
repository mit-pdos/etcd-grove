/-
Lean-first (no Rocq counterpart). Trace-check's layer D, S7 (part 1) (2026-11-11).

`RunConcurrent(cfg)` (`examples/raft/tracecheck/concurrent.go`): starts `cfg.Nodes` voters
(`StartNode`, each logging to the cluster's `SyncRecorder`), their application goroutines, the
isolation driver and the proposer, lets the cluster settle, stops it, and returns it with a nil
error. Its spec, for the workload the closed theorem runs (`Workload`: three voters, no
empty node, no configuration change, no snapshot, a delay bound `below` can draw from): it returns
`(c, nil)` with the run over (`runOver c`): `c.rec` is a recorder of a trace `γt`, and the caller
holds a view shift that, at the recorder's half of the trace `L` (under the recorder's lock, where
`Events` runs it), gives `RunOk L` (the whole trace parses, layer B's run goes through every line,
and its events have the facts the simulation keeps: `MainPure.lean`).

The premises: package initialization, `context`'s `isClosedchanInit` (the proposer's
`context.WithTimeout(context.Background(), ...)`, as `raft_kv.Main.spec`), the bootstrap log's facts
and premise (`tracecheck.BootLogFacts boot`, `tracecheck.premises boot`: `proto.Marshal`'s contract
at its conf changes, `Defs.lean`), the time receipts' bound past the bootstrap log
(`receiptBound GF + 3 ≤ 2^61`: the traced cluster's `cluster_alloc` with the voters' three bootstrap
entries, raft's `readyFits`), and the thread bound `ThreadBoundLe GF (2^31)` (the network's
`sync.WaitGroup` counts a goroutine per message in flight, and panics past `2^31`: `NetJoin.lean`).
With the adequacy theorem's `receiptBound = n + 1` and `threadBound = n + 2`, executions of
`n + 2 ≤ 2^31` steps (Q38, 2026-11-11).

Proved (2026-11-12, `Proof/.../tracecheck/RunConcurrent.lean`), over the traced node API's
statements (`HarnessDefs.lean`, `HarnessApi`; `Results.lean`, `HarnessOpen`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Recorder
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.MainPure
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Defs
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [GooseExts]

/-- The harness's types, by their short names. -/
abbrev G.Cluster := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster
abbrev G.CConfig := github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.CConfig

/-- **The workload the closed theorem runs**: three voters and no other node, no configuration
change, no snapshot (the simulation's premises: no restart, compaction or `ChangeConf`), and a
delay bound the network's `below(int(MaxDelay)+1)` can draw from (`below(0)` divides by zero), and
(Q35 (a), 2026-11-12) a positive tick (`time.NewTicker` panics otherwise). -/
def Workload (cfg : G.CConfig) : Prop :=
  cfg.Nodes' = W64 3 ∧ cfg.ExtraNodes' = 0 ∧ cfg.ConfChanges' = 0 ∧ cfg.SnapshotEvery' = 0 ∧
    0 ≤ sint.Z cfg.MaxDelay' ∧ sint.Z cfg.MaxDelay' < 2 ^ 62 ∧ 0 < sint.Z cfg.Tick'

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- **The run is over**: `c.rec` is a recorder of the trace `γt`, and at the recorder's half of the
trace `L` the caller learns `RunOk L` (once: the view shift `Events` runs under the lock). -/
def runOver (c : Loc) : IProp GF :=
  iprop(∃ (γt : GName) (r : Loc), c.[G.Cluster, go!"rec"] ↦□ r ∗ isSyncRecorder γt r ∗
    (∀ L, traceAuth γt L ={⊤}=∗ traceAuth γt L ∗ ⌜RunOk L⌝))

end spec

section spec2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- See the file header. -/
abbrev RunConcurrent.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)], receiptBound GF + 3 ≤ 2 ^ 61 →
  ∀ (boot : List LogEntry), tracecheck.BootLogFacts boot →
  ∀ (cfg : G.CConfig), Workload cfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
      context.isClosedchanInit ∗ tracecheck.premises boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.RunConcurrent)) (Val #cfg))
  {{ (c : Loc), RET (PairV #c #interface.nil); runOver c }}

end spec2

end TraceCheck
end EtcdGrove
end Perennial
