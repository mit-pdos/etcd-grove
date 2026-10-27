/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Periodic__Run.lean`. Lean-first (no Rocq
counterpart). The spec-first pilot's phase 1 (`notes/compactor-pilot-plan.md`): the spec is written,
the proof is phase 3's full proof (`sorry` until then).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__Run
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getCompactInterval
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getRetryInterval
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getRetentions
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Error
public import Spec.errors.Is

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api v3compactor

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

theorem v3compactor.Periodic.Run.wp_proof
    (hPeriodic_getCompactInterval : v3compactor.Periodic.getCompactInterval.spec (GF := GF) (hG := hG))
    (hPeriodic_getRetryInterval : v3compactor.Periodic.getRetryInterval.spec (GF := GF) (hG := hG))
    (hPeriodic_getRetentions : v3compactor.Periodic.getRetentions.spec (GF := GF) (hG := hG))
    (hInt64 : zap.Int64.spec (GF := GF) (hG := hG))
    (hDuration : zap.Duration.spec (GF := GF) (hG := hG))
    (hLogger_Info : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hLogger_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG)) :
    v3compactor.Periodic.Run.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
