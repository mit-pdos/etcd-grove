/-
`(*concurrency.Mutex).IsOwner` (`client/v3/concurrency/mutex.go`).

Users: `server/etcdserver/api/v3lock/lock.go:45` (`NewMutex(s, req.Name)`, `Lock(ctx)`, then
`Key()` and `Header()` returned to the remote client, which fences its writes on the key and
`Unlock`s by deleting it), etcdctl's `lock` command (not in the pinned sources: `Lock`, the key,
`Unlock`), recipes' callers, etcd's tests (`tests/integration/clientv3/concurrency/mutex_test.go`,
`example_mutex_test.go`: `Lock`, `TryLock` and `ErrLocked`, `IsOwner` in a `Txn`, `Unlock`,
`NewLocker`). Snippet: `concurrency/mutex.go` (`ReqFencedWrite`).

Proof sketch: `CreateRevision.spec`, `Compare.spec` (W0) with an `int64` (`CmpArg.i64`).

Changes: from `specs-ref`'s `Mutex__IsOwner.lean`: over W0's `cmpAt`; unchanged.

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

/-- `m.IsOwner()`: the comparison `CreateRevision(myKey) = myRev`, the fence of writes made while holding the lock. -/
def Mutex.IsOwner.spec : Prop :=
  ∀ (m : Loc) (st : MutexSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ mutexSt m st }}
    (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Mutex.ty @!! go!"IsOwner")) (Val #()))
  {{ (c : go_etcd_io.etcd.client.v3.Cmp), RET #c; mutexSt m st ∗ cmpAt c (some (ownerCmp st.key st.rev)) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
