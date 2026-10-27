/- Lean-first (no Rocq counterpart).

## `Main()` (check.go), the top-level driver

`StartCluster([]uint64{1, 2, 3})`, then `Check(kvs, lintest.CounterClock(), 4, 25)`, the
randomized linearizability test, then a panic unless porcupine answers `Ok`. It returns: it
never panics, so porcupine's check of the recorded trace always passes. Everything else (the
storage registry; raft's ghost state, budget and credits; the store's invariant; the clock) is
allocated in the proof, from what package initialization provides (`isPkgInit` of the store's
package, which holds its dependencies', raft's, lintest's and porcupine's among them) and
`context`'s `isClosedchanInit` (which porcupine's `WithCancel(Background())` needs and
`isPkgInit` does not give; the adequacy theorem gets it from the program's initialization,
`Init.lean`). For executions of fewer than `2^63` steps (`receiptBound GF ≤ 2^63`: the
counter clock does not wrap, and raft's terms stay below `2^64`).
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Defs
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness ∗ context.isClosedchanInit }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvwitness.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end kvwitness
end EtcdGrove
end Perennial
