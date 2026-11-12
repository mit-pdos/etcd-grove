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
pending jobs (with the cancelled context) and exited; and (2026-10-30, the repair, T1b) with the
last tracked job's postcondition (the queue's last saved proposition: its `Post`, or the initial
`True`): every pending job ran before `donec` closed (`schedule.go:150-184`); and (M2, the storage
side, 2026-10-30: review round 3's F2, the user's Q6) taking the payload (`schedPay γ`: `Stop`
cancels the context, done with it) and returning the run token (`schedDone γ`: the worker has
exited, so no job runs or will run). -/
abbrev schedule.Scheduler.Stop.spec : Prop :=
  ∀ (fi : GoInterfaceOk) (γ : schedule.SchedNames) (Ps : List GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗
      schedule.isFifo (GoInterface.ok fi) γ ∗ schedule.schedStopTok γ ∗ schedule.schedQueue γ Ps ∗
      schedule.schedPay γ }}
    (App (Val #(methods fi.ty go!"Stop" fi.v)) (Val #()))
  {{ RET #(); (match Ps.getLast? with
      | none => iprop(True)
      | some p => iprop(∃ P : IProp GF, schedule.savedProp p P ∗ ▷ P)) ∗
      schedule.schedDone γ }}

end spec

end EtcdGrove
end Perennial
