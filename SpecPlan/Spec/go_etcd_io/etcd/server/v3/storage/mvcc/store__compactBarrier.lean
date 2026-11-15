/-
`(*store).compactBarrier(ctx, ch)` (`kvstore.go:137`). Internal: the job `updateCompactRev`
schedules for a compaction at or below the last (its channel closed after the jobs before it), and
`compact`'s job on a failed or cancelled compaction.

**Proof sketch**: the context not done: `close(ch)` (`compactCh`). Done: the scheduler's context is
cancelled only by `Stop`, which `Close` and `Restore` call after closing `s.stopc`
(`Schedule.schedCtx`'s `Pay`, `storeStopped`), so the `select` takes `<-s.stopc` and returns; its
`default` branch (lock `s.mu`, schedule again) is unreachable, so the scheduler is never used after
`Stop` (`fifo.Schedule` would panic).

**Changes** from `specs-ref`'s file: over `InternalStore.lean` (`schedCtx` in place of
`barrierCtx`/`schedPay`, `compactCh` in place of `compactCloser`); `ctx` any value the scheduler hands
a job.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.compactBarrier(ctx, ch)` under the scheduler's context (done only once the store is
stopped): closes `ch`, or (stopped) returns. -/
def store.compactBarrier.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (ctx : GoInterface) (ch : GoChan),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ isStore s γ ∗
      Schedule.schedCtx ctx (storeStopped s γ) ∗ compactCh ch }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compactBarrier")) (Val #ctx))
      (Val #ch))
  {{ RET #(); True }}

end spec
end Mvcc
end EtcdGrove
end Perennial
