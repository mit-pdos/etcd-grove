/- Lean-first (no Rocq counterpart). The proof of `runner.startReaders`: Draft, to come.

The outline: `readStop.Store(0)` in its invariant (`rdShared`); `x.ms` is `[mp0, mp1]`
(`runnerMs`); for each member and each of the `max 0 cfg.Readers` iterations, the join's `Add(1)`
(`sync.tokJoin.WaitGroup.wp_Add`, the writer's thread token deposited) with `P' :=` the reader's
part less its handles, then `go` (the fresh token back to the writer); the goroutine's loop
(`readStop.Load`, `readOne`, `reads.Add(1)` in `rdShared`'s invariants, `time.Sleep`) keeps its
`rdOwn`, and its `Done` (`wp_Done`) gives the part back. The parts are `rdStock`'s split at `q / n`
(`rdStock_split`, `n > 0`; at `n = 0` the stock stays in the adder's wand). Perennial's results
(`Int64.Load/Store/Add`, `time.Sleep`, the join's `Add`/`Done`) are used directly. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__startReaders
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__readOne

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem runner.startReaders.wp_proof
    (wp_readOne : runner.readOne.spec (GF := GF) (hG := hG)) :
    runner.startReaders.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
