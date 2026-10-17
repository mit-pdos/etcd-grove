/-
`Scheduler.Pending` on the scheduler `NewFIFOScheduler` returns: the trust boundary (`fifo`'s
methods are names-only). Lean-first (2026-10-17, the verification of etcd-io/etcd#22496: the
server's `run` reports `sched.Pending()` in the gauge `applyBatchPending` after each `Schedule`).
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

/-- **`f.Pending()`** returns some count (the number of jobs in the queue, the running one
included, as `fifo.Pending` reads `len(f.pendings)` under `f.mu`), at any time (before or after
`Stop`), with no resource: the count is only reported (a metric). -/
abbrev schedule.Scheduler.Pending.spec : Prop :=
  ∀ (fi : GoInterfaceOk) (γ : schedule.SchedNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule ∗
      schedule.isFifo (GoInterface.ok fi) γ }}
    (App (Val #(methods fi.ty go!"Pending" fi.v)) (Val #()))
  {{ (n : w64), RET #n; True }}

end spec

end EtcdGrove
end Perennial
