/-
`concurrency.NewMutex(s, pfx)` (`client/v3/concurrency/mutex.go`).

Users: `server/etcdserver/api/v3lock/lock.go:45` (`NewMutex(s, req.Name)`, `Lock(ctx)`, then
`Key()` and `Header()` returned to the remote client, which fences its writes on the key and
`Unlock`s by deleting it), etcdctl's `lock` command (not in the pinned sources: `Lock`, the key,
`Unlock`), recipes' callers, etcd's tests (`tests/integration/clientv3/concurrency/mutex_test.go`,
`example_mutex_test.go`: `Lock`, `TryLock` and `ErrLocked`, `IsOwner` in a `Txn`, `Unlock`,
`NewLocker`). Snippets: `concurrency/mutex.go`.

Proof sketch: the struct allocated; `s` and `pfx + "/"` persisted (`isMutex`), the rest owned.

Changes: from `specs-ref`'s `NewMutex.lean`: no client premise (the old `isEtcdMutexClient` and
prefix bound): the constructor only stores; the methods take the session.

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

/-- `NewMutex(s, pfx)`: a mutex on the prefix `pfx + "/"`, not held. -/
def NewMutex.spec : Prop :=
  ∀ (s : Loc) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.NewMutex)) (Val #s)) (Val #pfx))
  {{ (m : Loc), RET #m; isMutex m s (pfx ++ go!"/") ∗ mutexSt m MutexSt.init }}

end spec

end Concurrency
end EtcdGrove
end Perennial
