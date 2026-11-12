/-
`SetProgressReportInterval(d)` (`watch.go`): sets the progress interval.

**Users.** `NewWatchServer` (`watch.go:87`, with the configured interval raised to 100ms); tests
(`tests/integration`, with small intervals such as `200ms`).

**Proof sketch.** `progressReportIntervalMu.Lock()` (the package's lock, `isPkgInit`), the write,
`Unlock`, the invariant kept: `progressIntervalOk d`.

**Changes** from `specs-ref`'s file: `watchVars` folded into `isPkgInit`; the bounds `10 ≤ d ≤
2 ^ 62` relaxed to what `GetProgressReportInterval` and the ticker need (`progressIntervalOk`:
`10 ≤ d`, `d + d / 10 ≤ 2 ^ 63`).

**Margin.** The premise is the lock invariant's (the call itself cannot fail); an interval below
`10` ns would make every later watch stream's send loop panic (`rand.Int63n(0)`), one above about
265 years every ticker (`nonissues/etcd-watch-progress-interval-overflow.md`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ApiWatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`SetProgressReportInterval(d)`** of an interval within the lock's invariant. -/
def SetProgressReportInterval.spec : Prop :=
  ∀ (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      ⌜progressIntervalOk (sint.Z d)⌝ }}
    (App (Val (@! v3rpc.SetProgressReportInterval)) (Val #d))
  {{ RET #(); True }}

end spec

end V3rpc
end EtcdGrove
end Perennial
