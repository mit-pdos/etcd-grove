/-
`Scheduler.Schedule` on the scheduler `NewFIFOScheduler` returns: the trust boundary (`fifo`'s
methods are names-only). Lean-first (2026-10-13, mvcc's compaction, unit 5a; the shape agreed
with the session verifying the server, which will strengthen it in place with the FIFO order:
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

/-- **`f.Schedule(j)`** of a job `j` (`jobIs γ j Pre Post`: its `Do`, with the scheduler's run
token and `Pre`, for any context, returns the token and `Post`) with its precondition `Pre`:
the scheduler takes `Pre` and runs the job later, once, in its goroutine (with the run token,
not overlapping another job). `Schedule` does not need the run token (a running job schedules
another: compaction's `compactBarrier`); nothing is returned (the job's `Post` is the job's,
not the caller's: a job hands its results over through its own resources, as compaction's
channel). -/
abbrev schedule.Scheduler.Schedule.spec : Prop :=
  ∀ (fi : GoInterfaceOk) (γ : schedule.SchedNames) (j : GoInterface) (Pre Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗
      schedule.isScheduler (GoInterface.ok fi) γ ∗ schedule.jobIs γ j Pre Post ∗ Pre }}
    (App (Val #(methods fi.ty go!"Schedule" fi.v)) (Val #j))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
