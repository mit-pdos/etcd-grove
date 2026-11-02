/- kvreconf's, with the files. Lean-first (no Rocq counterpart).

## `Main(dir)` (check.go), the top-level driver

`Run(RandomConfig(), lintest.CounterClock(), dir)`, the randomized linearizability test of a cluster
of random options under configuration changes, leadership disruptions and crashes (each crashed
replica restarted from its file in `dir`), then a panic unless porcupine answers `Ok`, then
`c.Stop()`. It returns: it never panics, so porcupine's check of the recorded trace always passes.

From the program's files (`durableOwn fs`, the program's half of the durable-state extension's
files: what the closed theorem's initial state gives), none of which is a replica's file in `dir`
(`kdFileName dir i` for the ids `i` in `1 … 9`, the program's precondition "`dir` holds none of the
replicas' files"; the directory itself is no notion of the extension: its files are a flat map from
names). Everything else (the files' invariant; the storage registry `kdStorInv`; raft's ghost state;
the store's invariant; the clock) is allocated in the proof, from what package initialization
provides (`isPkgInit` of the store's package, which holds its dependencies', raft's, lintest's,
porcupine's and `durable`'s among them) and `context`'s `isClosedchanInit`. For executions of fewer
than `2^61` steps (`receiptBound GF ≤ 2^61`: the counter clock does not wrap, raft's step bound
`2^64 - 2` holds, and raft's `RestartNode` has its `readyFits`; until 2026-11-02, stage II (t),
`2^63`, as kvreconf's `Main`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Alloc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ (dir : GoString) (fs : DurableState),
  receiptBound GF ≤ 2 ^ 61 → (∀ i ∈ kvreconf.allIds, fs !! kdFileName dir i = none) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗
      context.isClosedchanInit ∗ durableOwn fs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvdurable.Main)) (Val #dir))
  {{ RET #(); True }}

end spec

end kvdurable
end EtcdGrove
end Perennial
