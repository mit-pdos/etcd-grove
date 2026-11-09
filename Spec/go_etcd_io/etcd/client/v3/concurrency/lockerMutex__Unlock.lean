/-
`(*concurrency.lockerMutex).Unlock` (`client/v3/concurrency/mutex.go`).

Users: `server/etcdserver/api/v3lock/lock.go:45` (`NewMutex(s, req.Name)`, `Lock(ctx)`, then
`Key()` and `Header()` returned to the remote client, which fences its writes on the key and
`Unlock`s by deleting it; the in-process client: each request's principal is the RPC context's),
etcdctl's `lock` command (not in the pinned sources), etcd's tests
(`tests/integration/clientv3/concurrency/mutex_test.go`, `example_mutex_test.go`: `Lock`, `TryLock`
and `ErrLocked`, `IsOwner` in a `Txn`, `Unlock`, `NewLocker`; `tests/integration/v3lock_grpc_test.go`:
a second lock's header after the first's). Snippet: `concurrency/mutex.go` (`ReqLocker`).

Proof sketch: the embedded field (`↦□`), `isSession_client`, `Client.Ctx.spec` (1c: the client's
context, `ctxPrin` of its principal `who`), `Mutex.Unlock.spec`; on an error `panic(err)` (Perennial's
panic outcome).

Changes: from `specs-ref`'s `lockerMutex__Unlock.lean`: as `Mutex.Unlock`.

Changes: verify-round: returns only on a held mutex (as `Mutex.Unlock.spec`'s `nil`, A3 F1); on a released one it panics with `ErrLockReleased`.

Margin: the panic carries the error; the caller (a `sync.Locker` user) cannot recover it usefully.
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

/-- `l.Unlock()`: `Mutex.Unlock` with the client's context; it returns released, or panics with the error. -/
def lockerMutex.Unlock.spec : Prop :=
  ∀ (lm m s c : Loc) (pfx : GoString) (st : MutexSt) (γ : Cluster) (dflt who : Principal) (id : w64)
    (T : State → State → Prop) (P : IProp GF) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ lm.[go_etcd_io.etcd.client.v3.concurrency.lockerMutex, go!"Mutex"] ↦□ m ∗ isMutex m s pfx ∗ mutexSt m st ∗
      isSession s c γ id ∗ isClient c γ dflt ∗ etcdLent γ T P ∗ P ∗ etcdLb γ σ0 ∗ ⌜effIn (delEff (fun k => k = st.key ∧ pfx <+: k)) T⌝ }}
    (App (Val (lm @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.lockerMutex.ty @!! go!"Unlock")) (Val #()))
  {{ (r : val), RET r;
      (⌜r = #() ∧ ¬ (st.key = [] ∨ sint.Z st.rev ≤ 0 ∨ st.key = [W8 0])⌝ ∗ P ∗ ∃ σ : State, etcdLb γ σ ∗ ⌜Reach σ0 σ ∧ σ.kv.store st.key = none⌝ ∗ mutexSt m st.released) ∨
      (⌜∃ err : GoInterface, err ≠ GoInterface.nil ∧ r = PanicV #err⌝ ∗ mutexSt m st) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
