/-
## `monitorFileDescriptor(lg, done)` (`metrics.go:215-245`)

**Users.** `Start` (attached goroutine, with `s.Logger()` and `s.stopping`).

**Proof sketch.** A ticker loop (Perennial's `time`), `runtime.FDUsage` (trusted: it returns an
error or a count), a log line; returns when `done` closes (`stoppingCh`).

**Changes**: from `specs-ref`'s `monitorFileDescriptor.lean`: the stopping channel's predicate.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Logs file-descriptor usage** until `done` closes. -/
def monitorFileDescriptor.spec : Prop :=
  ∀ (lg done : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ Zap.isLogger lg ∗ stoppingCh done }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.monitorFileDescriptor)) (Val #lg)) (Val #done))
  {{ RET #(); True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
