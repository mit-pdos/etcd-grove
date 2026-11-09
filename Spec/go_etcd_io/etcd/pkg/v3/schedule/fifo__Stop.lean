/-
`(*fifo).Stop()` (`schedule.go`): cancels the context, sets `cancel = nil` (a later `Schedule`
panics), and waits for `donec`, which the worker closes after running every pending job.

**Users**: through `isSched`'s `Stop` row: `run`'s deferred shutdown (`server.go:798`), mvcc's
`store.Close`/`Restore` (`kvstore.go:302, 309`). Snippet `ReqStopRunsPending`.

**Proof sketch**: with `schedOpen γ 1` put back into the lock invariant (no `Schedule` can run, so
the queue is final) and `□ Pay` given to the context's done-ness, call `cancel` (`cancelOk`); the
worker sees the context done, runs the pending jobs (each with `schedCtx`, whose done-ness gives
`□ Pay`), and closes `donec` carrying the last post, which `schedTail γ P` names: the receive gives
`P`.

**Changes**: `schedStopTok`/`schedQueue`/`schedPay` become `schedOpen γ 1`, `schedTail γ P`, `□ Pay`;
the run token `schedDone` is dropped (no user needs it: no user resource is lent to the worker
outside its jobs). **Margin**: none.
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

/-- **Stop**: every pending job has run; the chain's end `P` comes back. -/
def fifo.Stop.spec : Prop :=
  ∀ (l : Loc) (γ : SchedNames) (Pay P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗ isFifo l γ Pay ∗
      schedOpen γ 1 ∗ schedTail γ P ∗ □ Pay }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.schedule.fifo.ty @!!
      go!"Stop")) (Val #()))
  {{ RET #(); P }}

end spec
end Schedule
end EtcdGrove
end Perennial
