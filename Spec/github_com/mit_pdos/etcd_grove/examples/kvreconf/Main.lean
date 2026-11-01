/- Lean-first (no Rocq counterpart).

## `Main()` (check.go), the top-level driver

`Run(RandomConfig(), lintest.CounterClock())`, the randomized linearizability test of a cluster of
random options under configuration changes and leadership disruptions, then a panic unless
porcupine answers `Ok`, then `c.Stop()`. It returns: it never panics, so porcupine's check of the
recorded trace always passes. Everything else (the storage registry `kvrStorInv`; raft's ghost
state; the store's invariant; the clock) is allocated in the proof, from what package
initialization provides (`isPkgInit` of the store's package, which holds its dependencies', raft's,
lintest's and porcupine's among them) and `context`'s `isClosedchanInit` (which porcupine's
`WithCancel(Background())` needs and `isPkgInit` does not give). For executions of fewer than
`2^63` steps (`receiptBound GF ≤ 2^63`: the counter clock does not wrap, and raft's step bound
`2^64 - 2` holds), as kv's `Main`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗
      context.isClosedchanInit }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end kvreconf
end EtcdGrove
end Perennial
