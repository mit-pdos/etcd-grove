/-
`GetProgressReportInterval()` (`watch.go`): the progress interval with a jitter.

**Users.** `sendLoop` (`watch.go:419`: the ticker's period); tests.

**Proof sketch.** `progressReportIntervalMu.RLock()` (the package's lock, its invariant
`progressIntervalOk` of `progressReportInterval`, part of v3rpc's initialized state, `isPkgInit`:
the initializer's 10 minutes meets it; the thread token as the reader slot), the read, `RUnlock`;
`rand.Int63n(interval / 10)` (Perennial's `math/rand`: a positive bound, `interval ≥ 10`; a value
in `[0, interval / 10)`); the sum, positive and without overflow (`interval + interval / 10 ≤
2 ^ 63`).

**Changes** from `specs-ref`'s file: the thread pool of the interval's reader slots and the
`threadBound` premise (`v3rpc.intervalPool`, `watchVars`) folded into `isPkgInit` and the thread
token (the bounds plan: the owner turns the slots into a protocol over thread tokens).

**Margin.** The value is in `[interval, interval + interval / 10)`; only positivity is stated (the
ticker's need; no caller relies on the period).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ApiWatch

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

/-- **`GetProgressReportInterval()`**: a positive duration. -/
def GetProgressReportInterval.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      threadTok }}
    (App (Val (@! v3rpc.GetProgressReportInterval)) (Val #()))
  {{ (d : w64), RET #d; ⌜0 < sint.Z d⌝ ∗ threadTok }}

end spec

end V3rpc
end EtcdGrove
end Perennial
