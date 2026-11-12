/- Lean-first (no Rocq counterpart).

`x.startReaders()` (`examples/mvccfull/mvccfull.go`): clears the stop flag and starts
`cfg.Readers` readers on each member (`n = 2 * max 0 cfg.Readers` goroutines), each running up to
`cfg.Reads` reads (`readOne`, counted in `x.reads`, with a `ReadPause` sleep) until the flag is set.

**The triple.** The writer, with its thread token and the readers' wait group's join at rest
(`sync.tokJoin.ownAdder rdWgN False x.readWg 0 True`: no reader running), lends the `n` readers'
parts (`rdStock`: `n` history slots; for each member's current incarnation, `n` reader tokens and a
share `q` of its retirement token and `kv` field), with the incarnations' handles, the run's
read-only fields and its shared atomics (`rdShared`). Each reader gets its part (`rdStock_split`, at
the share `q / n`) and, at its `Done`, gives it back. So `startReaders` returns the thread token
and the join with `n` readers whose `Done`s give back the stock (`stopReaders` then returns it).
F1's scope premise (`readMixOk`) is `readOne`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Readers
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev runner.startReaders.spec : Prop :=
  ∀ (x : Loc) (cfg : Config) (wr : List w64) (ks : List GoString) (h : Loc) (γ : FullNames)
    (mp0 mp1 : Loc) (e0 e1 : IncNames × GoInterface) (q : Qp),
  readMixOk (wr.map sint.Z) →
  let n := 2 * (sint.Z cfg.Readers').toNat
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗
      runnerKeys x ks ∗ runnerH x h ∗ runnerCfg x cfg wr ∗ runnerMs x mp0 mp1 ∗ rdShared x ∗
      isInc ks γ.h 0 mp0 γ.m0 e0.1 e0.2 ∗ isInc ks γ.h 1 mp1 γ.m1 e1.1 e1.2 ∗
      rdStock h γ mp0 mp1 e0 e1 n q ∗
      sync.tokJoin.ownAdder rdWgN iprop(False) (rF go!"readWg" x) 0 iprop(True) ∗ threadTok }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"startReaders") (Val #()))
  {{ RET #(); threadTok ∗
      sync.tokJoin.ownAdder rdWgN iprop(False) (rF go!"readWg" x) n
        (rdStock h γ mp0 mp1 e0 e1 n q) }}

end spec

end mvccfull
end EtcdGrove
end Perennial
