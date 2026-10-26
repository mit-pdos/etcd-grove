/-
`Scheduler.Stop` on the scheduler `NewFIFOScheduler` returns, proved from `(*fifo).Stop` since
2026-10-22 (the trust boundary until then, when `fifo`'s methods were names-only). Lean-first (2026-10-13, the request path's unit 4c: the server's `run`
stops its scheduler in its deferred shutdown).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

/-- **`f.Stop()`**, with the stop token and the queue (so no `Schedule` follows: an untracked one
needs `schedLive`, which the stop token excludes, a tracked one the queue; `fifo.Schedule` after
`Stop` panics): it cancels the scheduler's context and returns once its goroutine has run the
pending jobs (with the cancelled context) and exited. -/
abbrev schedule.Scheduler.Stop.spec : Prop :=
  ∀ (fi : GoInterfaceOk) (γ : schedule.SchedNames) (Ps : List GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗
      schedule.isFifo (GoInterface.ok fi) γ ∗ schedule.schedStopTok γ ∗ schedule.schedQueue γ Ps }}
    (App (Val #(methods fi.ty go!"Stop" fi.v)) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
