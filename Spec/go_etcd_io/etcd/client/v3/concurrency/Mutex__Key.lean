/-
`(*concurrency.Mutex).Key` (`client/v3/concurrency/mutex.go`).

Users: `server/etcdserver/api/v3lock/lock.go:45` (`NewMutex(s, req.Name)`, `Lock(ctx)`, then
`Key()` and `Header()` returned to the remote client, which fences its writes on the key and
`Unlock`s by deleting it; the in-process client: each request's principal is the RPC context's),
etcdctl's `lock` command (not in the pinned sources), etcd's tests
(`tests/integration/clientv3/concurrency/mutex_test.go`, `example_mutex_test.go`: `Lock`, `TryLock`
and `ErrLocked`, `IsOwner` in a `Txn`, `Unlock`, `NewLocker`; `tests/integration/v3lock_grpc_test.go`:
a second lock's header after the first's). Snippet: `concurrency/mutex.go` (`ReqV3LockPattern`).

Proof sketch: the field, read.

Changes: from `specs-ref`'s `Mutex__Key.lean`: restated over `mutexSt`.

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

/-- `m.Key()`: the mutex's key (`""` before a lock, `"\x00"` after a release). -/
def Mutex.Key.spec : Prop :=
  ∀ (m : Loc) (st : MutexSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ mutexSt m st }}
    (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Mutex.ty @!! go!"Key")) (Val #()))
  {{ RET #(st.key); mutexSt m st }}

end spec

end Concurrency
end EtcdGrove
end Perennial
