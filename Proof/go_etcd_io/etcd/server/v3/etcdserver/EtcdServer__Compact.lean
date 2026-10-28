/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Compact.lean`. Lean-first (no Rocq
counterpart). The spec-first pilot's phase 1 (`notes/compactor-pilot-plan.md`): the glue over
`processInternalRaftRequestOnce`, `sorry` until the compaction request has a proposal permit
(`reqPropOk`'s compaction form, the server side's model step).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Compact
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Tracer__Start
public import Spec.go_opentelemetry_io.otel.trace.WithAttributes
public import Spec.go_opentelemetry_io.otel.attribute.Bool
public import Spec.go_opentelemetry_io.otel.attribute.Int64
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__processInternalRaftRequestOnce
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__GetStartTime
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__SetStartTime
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__InsertStep
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__LogIfLong
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.CompactionRequest__GetPhysical
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.CompactionRequest__GetRevision
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Rev

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.Compact.wp_proof
    (hStart : traceutil.Tracer.Start.spec (GF := GF) (hG := hG))
    (hWithAttr : trace.WithAttributes.spec (GF := GF) (hG := hG))
    (hBool : «attribute».Bool.spec (GF := GF) (hG := hG))
    (hInt64 : «attribute».Int64.spec (GF := GF) (hG := hG))
    (hPhys : CompactionRequest.GetPhysical.spec (GF := GF) (hG := hG))
    (hRev : CompactionRequest.GetRevision.spec (GF := GF) (hG := hG))
    (hLogger : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hPIRRO : EtcdServer.processInternalRaftRequestOnce.spec (GF := GF) (hG := hG))
    (hGetStart : traceutil.Trace.GetStartTime.spec (GF := GF) (hG := hG))
    (hSetStart : traceutil.Trace.SetStartTime.spec (GF := GF) (hG := hG))
    (hInsert : traceutil.Trace.InsertStep.spec (GF := GF) (hG := hG))
    (hLogIfLong : traceutil.Trace.LogIfLong.spec (GF := GF) (hG := hG))
    (hRevS : mvcc.store.Rev.spec (GF := GF) (hG := hG)) :
    EtcdServer.Compact.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
