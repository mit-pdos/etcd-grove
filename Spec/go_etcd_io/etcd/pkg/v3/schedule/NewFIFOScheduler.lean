/-
`schedule.NewFIFOScheduler(lg)` (`schedule.go`).

**Users**: `server.go:761` (`run`: the apply jobs' chain), `kvstore.go:107, 310` (mvcc's store:
compaction jobs, rebuilt at `Restore`). Snippets `examples/specreq/schedule/schedule.go`
(`ReqFifoChain`, `ReqStopRunsPending`, `ReqCancelledCtx`).

**Proof sketch**: `verify.Assert(lg != nil)` passes (`isLogger lg`); allocate the `fifo` (its
channels, `sync.NewCond`), `context.WithCancel(Background())` (`ctxOk`, `cancelOk`); allocate the
ghost state: `schedTail γ True`, `schedOpen γ 1`, and `isFifo`'s lock invariant with no pending job,
`cancel` live, the context's done-ness tied to `□ Pay` (only `Stop`, which takes `□ Pay`, calls
`cancel`); fork `run` with `fifoWorker` (`fifo.run.spec`). `isFifo_isSched` gives the bundle.

**Changes**: the old spec's queue of saved names (`schedQueue γ Ps`, `savedProp`) and its tracked /
untracked split (`schedPre`/`schedPost`, `schedLive`, `schedStopTok`) become one chain end
`schedTail γ P` and a fractional right `schedOpen` (an untracked user keeps the tail at `True`); the
payload `schedPayIs γ Pay` is the bundle's index `Pay`.

**Margin**: none (the metrics `Pending`/`Scheduled`/`Finished` are not modelled).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Schedule

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

/-- **A new FIFO scheduler** for a logger: the `Scheduler` bundle, the whole right to schedule, an
empty chain (`True`), for any `Pay` its context's being done will give. -/
def NewFIFOScheduler.spec : Prop :=
  ∀ (lg : Loc) (Pay : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗ Zap.isLogger lg }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.schedule.NewFIFOScheduler)) (Val #lg))
  {{ (sc : GoInterface), RET #sc; ∃ γ : SchedNames,
      isSched sc γ Pay ∗ schedOpen γ 1 ∗ schedTail γ iprop(True) }}

end spec
end Schedule
end EtcdGrove
end Perennial
