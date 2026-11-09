/-
`concurrency.NewLocker(s, pfx)` (`client/v3/concurrency/mutex.go`).

Users: `server/etcdserver/api/v3lock/lock.go:45` (`NewMutex(s, req.Name)`, `Lock(ctx)`, then
`Key()` and `Header()` returned to the remote client, which fences its writes on the key and
`Unlock`s by deleting it), etcdctl's `lock` command (not in the pinned sources: `Lock`, the key,
`Unlock`), recipes' callers, etcd's tests (`tests/integration/clientv3/concurrency/mutex_test.go`,
`example_mutex_test.go`: `Lock`, `TryLock` and `ErrLocked`, `IsOwner` in a `Txn`, `Unlock`,
`NewLocker`). Snippet: `concurrency/mutex.go` (`ReqLocker`).

Proof sketch: `NewMutex.spec`; the `lockerMutex` allocated, its field persisted.

Changes: from `specs-ref`'s `NewLocker.lean`: as `NewMutex`.

Margin: the result is a `sync.Locker` whose methods panic on any client error, so it is not
Perennial's `isLocker`; its concrete type is stated, and `lockerMutex.Lock`/`Unlock` are its
specs.
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

/-- `NewLocker(s, pfx)`: a `*lockerMutex` around a new mutex on `pfx + "/"`. -/
def NewLocker.spec : Prop :=
  ∀ (s : Loc) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.NewLocker)) (Val #s)) (Val #pfx))
  {{ (l : GoInterface), RET #l; ∃ lm m : Loc,
      ⌜l = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.lockerMutex.ty) #lm⌝ ∗
      lm.[go_etcd_io.etcd.client.v3.concurrency.lockerMutex, go!"Mutex"] ↦□ m ∗
      isMutex m s (pfx ++ go!"/") ∗ mutexSt m MutexSt.init }}

end spec

end Concurrency
end EtcdGrove
end Perennial
