/-
`(*concurrency.Session).Orphan` (`client/v3/concurrency/session.go`).

Users: `server/etcdserver/api/v3lock/lock.go:36` and `v3election/election.go:126` (`WithLease(req.Lease)`,
`WithContext(ctx)`, then `Orphan()`: a session over a lease the remote client holds, never
refreshed by the server; `Leader`/`Observe` pass lease `-1`; a session per RPC), `client/leasing/kv.go:147` (a
session per monitor round, in a loop, its `Done()` awaited), `server/proxy/grpcproxy/register.go:65`
(`WithTTL`, its lease on an endpoint key, `Close()` on error or shutdown, a new session per expiry), recipes
(`key.go:142`, `rwmutex.go:69`, `double_barrier.go:47`: `Client()` and `Lease()`), etcd's tests
(`tests/integration/clientv3/concurrency/session_test.go`). Snippet: `concurrency/session.go` (`ReqSessionResumeLease`, v3lock's pattern).

Proof sketch: the cancel function (`cancelOk`, `isSession`'s realization), then a receive on
`donec` (`broadcast_chan_receive`): it returns once the keep-alive goroutine closed it (partial
correctness: 1c's keep-alive channel closes once its context is done).

Changes: from `specs-ref`'s `Session__Orphan.lean`: restated over `isSession`.

Margin: the session's context is done afterwards; not stated (no user reads it).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Concurrency

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `s.Orphan()`: stops refreshing the lease and waits for the keep-alive to end. -/
def Session.Orphan.spec : Prop :=
  ∀ (s c : Loc) (γ : Cluster) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isSession s c γ id }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Session.ty @!! go!"Orphan")) (Val #()))
  {{ RET #(); True }}

end spec

end Concurrency
end EtcdGrove
end Perennial
