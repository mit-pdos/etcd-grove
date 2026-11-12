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
`context.WithTimeout(context.Background(), ...)`, as `raft_kv.Main.spec`), and the time receipts'
bound past the bootstrap log (`tcRunFits GF`, `receiptBound GF + 3 ≤ 2^61`, named since 2026-11-12,
`Fits.lean`: the traced cluster's `cluster_alloc`
with the voters' three bootstrap entries, raft's `readyFits`; with the adequacy theorem's
`receiptBound = n + 1`, executions of `n + 4 ≤ 2^61` steps).

Not proved yet (S7 (part 1) states it; its proof is the harness's, over the traced node API: the
recorder and the trace's names allocated, the traced cluster (`reTrace := some γd`), the shared
invariant `Cluster.traceSimInv_alloc`, three `StartNode`s with `startTrace`, the goroutines over the
traced `RawNode`/`node` triples, and at the end `Cluster.traceSimInv_end` with the bootstrap facts
(`MainSim.lean`, `runOk_of_sim`)). `Main`'s proof and the closed theorem take it as a hypothesis
(`Results.lean`, `raft_tracecheck_safe_of`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Recorder
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.MainPure
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Fits

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
delay bound the network's `below(int(MaxDelay)+1)` can draw from (`below(0)` divides by zero). -/
def Workload (cfg : G.CConfig) : Prop :=
  cfg.Nodes' = W64 3 ∧ cfg.ExtraNodes' = 0 ∧ cfg.ConfChanges' = 0 ∧ cfg.SnapshotEvery' = 0 ∧
    0 ≤ sint.Z cfg.MaxDelay' ∧ sint.Z cfg.MaxDelay' < 2 ^ 62

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

/-- See the file header. -/
abbrev RunConcurrent.spec : Prop :=
  tcRunFits GF →
  ∀ (cfg : G.CConfig), Workload cfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
      context.isClosedchanInit }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.RunConcurrent)) (Val #cfg))
  {{ (c : Loc), RET (PairV #c #interface.nil); runOver c }}

end spec

end TraceCheck
end EtcdGrove
end Perennial
