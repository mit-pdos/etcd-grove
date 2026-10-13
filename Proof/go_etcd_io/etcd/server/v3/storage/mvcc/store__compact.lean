/-
Proof of the spec of the same name: pending (the mvcc store's compaction, units 5b/5c; `sorry`).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__compact
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewJob
public import Spec.context.Err
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__compactBarrier
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__scheduleCompaction
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.hashStorage__Store
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Schedule
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.compact.wp_proof
    (h0 : schedule.NewJob.spec (GF := GF) (hG := hG))
    (h1 : context.Err.spec (GF := GF) (hG := hG))
    (h2 : mvcc.store.compactBarrier.spec (GF := GF) (hG := hG))
    (h3 : mvcc.store.scheduleCompaction.spec (GF := GF) (hG := hG))
    (h4 : zap.Error.spec (GF := GF) (hG := hG))
    (h5 : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (h6 : mvcc.hashStorage.Store.spec (GF := GF) (hG := hG))
    (h7 : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (h8 : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG))
    (h9 : traceutil.Trace.Step.spec (GF := GF) (hG := hG)) :
    mvcc.store.compact.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
