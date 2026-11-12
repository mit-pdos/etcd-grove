/-
`(*fifo).Schedule(j)` (`schedule.go`): appends the job to `pendings` under the lock, waking the
worker (a non-blocking send on `resume`) when the queue was empty.

**Users**: through the `Scheduler` interface (`isSched`'s `Schedule` row): `run` (`server.go:842`),
mvcc (`kvstore.go:148, 202, 247`). Snippets `ReqFifoChain`, `ReqCancelledCtx`.

**Proof sketch**: lock `mu`; `schedOpen γ q` shows `cancel != nil` (the invariant holds
`schedOpen γ 1` only once stopped), so no panic; the new pending job's saved pre is the old tail's
post `P` with `A`, its post `Q`; the tail moves to `Q` (a ghost variable); the send on `resume`
(capacity 1) never blocks (`select` with `default`); unlock.

**Changes**: one spec (was tracked/untracked, `schedPre`/`schedPost`). **Margin**: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.schedule.Api

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

/-- **Schedule a job** that turns the chain's end `P` (with `A`) into `Q`: the chain now ends at
`Q`; the job runs later, after every job scheduled before it, in the worker goroutine. -/
def fifo.Schedule.spec : Prop :=
  ∀ (l : Loc) (γ : SchedNames) (Pay : IProp GF) (j : GoInterface) (q : Qp) (P A Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗ isFifo l γ Pay ∗
      schedOpen γ q ∗ schedTail γ P ∗ jobOk j Pay iprop(P ∗ A) Q ∗ A }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.schedule.fifo.ty @!!
      go!"Schedule")) (Val #j))
  {{ RET #(); schedOpen γ q ∗ schedTail γ Q }}

end spec
end Schedule
end EtcdGrove
end Perennial
