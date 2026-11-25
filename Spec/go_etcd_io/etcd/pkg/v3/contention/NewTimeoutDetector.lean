/-
`contention.NewTimeoutDetector(maxDuration)` (`pkg/contention/contention.go:37`; the package is
names-only): the trust boundary (premises to axioms, item D, 2026-11-24). Until then the closed theorems
took it as the Iris premise `rnTimeoutDetectorOk` (`InvNodeStart.lean`, now gone), whose triple this is,
unchanged: the detector it returns meets `isRNTimeoutDetector` (`InvRaftNode.lean`: `Reset` and
`Observe` return). `newRaftNode`'s proof takes it as a callee. Interim: retired by translating the
package with its bodies (40 Go lines; plan item D).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `contention.NewTimeoutDetector(d)` returns a detector whose `Reset` and `Observe` return
(`isRNTimeoutDetector`), for any duration `d`.

Why it is true of Go (`contention.go` at the etcd pin): `NewTimeoutDetector` returns
`&TimeoutDetector{maxDuration: d, records: make(map[uint64]time.Time)}`, non-nil. `Reset` takes the
detector's mutex and replaces `records` with a new empty map; `Observe(which)` takes the mutex, reads
`time.Now()`, looks `which` up in `records`, computes the excess over `maxDuration` if present, stores
`now` under `which`, and returns `(ok, exceed)`. Neither can panic (a map of `uint64` keys, the mutex
held, `time.Time.Sub` total) nor block but on the mutex, which only these methods take and release
before returning. `isRNTimeoutDetector` claims only that they return. -/
abbrev contention.NewTimeoutDetector.spec : Prop :=
  ∀ d : time.Duration,
  {{ (True : IProp GF) }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.contention.NewTimeoutDetector)) (Val #d))
  {{ (td : Loc), RET #td; isRNTimeoutDetector td }}

end spec

end EtcdGrove
end Perennial
