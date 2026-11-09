/-
`concurrency.WithTTL(ttl)` (`client/v3/concurrency/session.go`).

Users: `server/etcdserver/api/v3lock/lock.go:36` and `v3election/election.go:126` (`WithLease(req.Lease)`,
`WithContext(ctx)`, then `Orphan()`: a session over a lease the remote client holds, never
refreshed by the server; `Leader`/`Observe` pass lease `-1`; a session per RPC), `client/leasing/kv.go:147` (a
session per monitor round, in a loop, its `Done()` awaited), `server/proxy/grpcproxy/register.go:65`
(`WithTTL`, its lease on an endpoint key, `Close()` on error or shutdown, a new session per expiry), recipes
(`key.go:142`, `rwmutex.go:69`, `double_barrier.go:47`: `Client()` and `Lease()`), etcd's tests
(`tests/integration/clientv3/concurrency/session_test.go`). Snippet: `concurrency/session.go` (`ReqSessionTTL`).

Proof sketch: a closure value; `sessOptAt`'s realization is its body's triple: `ttl > 0` writes the
field; otherwise `zap.Int64.spec` and `Zap.Logger.Warn.spec` (the logger `sessOptAt_call` takes).

Changes: from `specs-ref`'s `WithTTL.lean`: restated over `sessOptAt`/`withTTLM`; unchanged.

Margin: none.
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

/-- `WithTTL(ttl)`: an option setting the TTL if positive (else logging a warning). -/
def WithTTL.spec : Prop :=
  ∀ (ttl : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency }}
    (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.WithTTL)) (Val #ttl))
  {{ (f : GoFunc), RET #f; sessOptAt f (withTTLM ttl) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
