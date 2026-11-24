/-
`monitorFileDescriptor(lg, done)` (`metrics.go`): one of the goroutines `Start` attaches, with its body
(prove-ps2-srvgoroutines, 2026-11-24, etcd-grove#42; until then names-only, a trust-boundary axiom).
Lean-first (the request path's unit 4c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Spec.go_uber_org.zap.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopChan

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `monitorFileDescriptor(lg, done)` of a zap logger and a stop channel returns: it logs the file
descriptor usage (`runtime.FDUsage`, `runtime.FDLimit`, the gauges `fdUsed`/`fdLimit`) every ten
minutes until `done` is closed or a query fails. It calls `lg.Warn`, so a nil `lg` panics (the premise
since audit B4b, 2026-10-18; `zapLoggerOk` since premise fixes 6). (prove-ps2-srvgoroutines, 2026-11-24)
`done` is a stop channel (`stopChan`: `Start` passes `s.stopping`), the receive the loop's `select`
waits on; until then the contract was a names-only axiom with no fact on `done`. -/
abbrev monitorFileDescriptor.spec : Prop :=
  ∀ (lg : Loc) (done : GoChan),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ zapLoggerOk lg ∗
      stopChan done }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.monitorFileDescriptor)) (Val #lg))
      (Val #done))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
