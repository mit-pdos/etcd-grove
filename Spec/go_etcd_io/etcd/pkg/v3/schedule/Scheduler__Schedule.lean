/-
`Scheduler.Schedule` on the scheduler `NewFIFOScheduler` returns: the trust boundary (`fifo`'s
methods are names-only). Lean-first (2026-10-13, mvcc's compaction, unit 5a; strengthened in place
with the FIFO order by the request path's unit 4c, 2026-10-13, as agreed with the mvcc session:
`Proof/go_etcd_io/etcd/pkg/v3/schedule/Defs.lean`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

/-- **`f.Schedule(j)`** of a job `j` (`jobIs γ j Pre Prev Post`: its `Do`, with the scheduler's
run token, `Pre` and `Prev`, for any context, returns the token and `Post`) with its
precondition `Pre`: the scheduler takes `Pre` and runs the job later, once, in its goroutine,
after every job scheduled before it (FIFO; with the run token, not overlapping another job).
Tracked (`tr = some (Ps, prev, post)`): the caller's queue ends with `prev`, which saves `Prev`
(the `Post` of the tracked job scheduled before, or the initial `True`), and `post` saves the
job's `Post`; the worker hands the job `Prev` and keeps its `Post` for the next tracked job; the
caller gets the queue back with `post` appended. Untracked (`tr = none`): `Prev = Post = True`,
and the scheduler is never stopped (`schedLive`: a `Schedule` after `Stop` panics). `Schedule`
does not need the run token (a running job schedules another: compaction's
`compactBarrier`). True of `fifo` (`pkg/schedule/schedule.go`): one worker goroutine runs the
pending jobs in order, `Stop` runs the pending ones before it returns. -/
abbrev schedule.Scheduler.Schedule.spec : Prop :=
  ∀ (fi : GoInterfaceOk) (γ : schedule.SchedNames) (j : GoInterface) (Pre Prev Post : IProp GF)
    (tr : Option (List GName × GName × GName)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗
      schedule.isFifo (GoInterface.ok fi) γ ∗ schedule.jobIs γ j Pre Prev Post ∗ Pre ∗
      schedule.schedPre γ tr Prev Post }}
    (App (Val #(methods fi.ty go!"Schedule" fi.v)) (Val #j))
  {{ RET #(); schedule.schedPost γ tr }}

end spec

end EtcdGrove
end Perennial
