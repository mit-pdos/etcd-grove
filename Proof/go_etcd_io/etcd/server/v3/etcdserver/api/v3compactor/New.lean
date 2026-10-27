/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/New.lean`. Lean-first (no Rocq
counterpart). The spec-first pilot's phase 1 (`notes/compactor-pilot-plan.md`): the spec is written,
the proof is phase 1's glue (`sorry` until written).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.New
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.jonboulle.clockwork.NewRealClock
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newPeriodic
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.newRevision
public import Spec.fmt.Errorf
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__Run
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__Stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__Pause
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__Resume
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision__Run
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision__Stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision__Pause
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision__Resume

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

theorem v3compactor.New.wp_proof
    (hNewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (hNewRealClock : clockwork.NewRealClock.spec (GF := GF) (hG := hG))
    (hnewPeriodic : v3compactor.newPeriodic.spec (GF := GF) (hG := hG))
    (hnewRevision : v3compactor.newRevision.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (hPeriodic_Run : v3compactor.Periodic.Run.spec (GF := GF) (hG := hG))
    (hPeriodic_Stop : v3compactor.Periodic.Stop.spec (GF := GF) (hG := hG))
    (hPeriodic_Pause : v3compactor.Periodic.Pause.spec (GF := GF) (hG := hG))
    (hPeriodic_Resume : v3compactor.Periodic.Resume.spec (GF := GF) (hG := hG))
    (hRevision_Run : v3compactor.Revision.Run.spec (GF := GF) (hG := hG))
    (hRevision_Stop : v3compactor.Revision.Stop.spec (GF := GF) (hG := hG))
    (hRevision_Pause : v3compactor.Revision.Pause.spec (GF := GF) (hG := hG))
    (hRevision_Resume : v3compactor.Revision.Resume.spec (GF := GF) (hG := hG)) :
    v3compactor.New.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
