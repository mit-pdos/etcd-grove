/-
`(*concurrency.lockerMutex).Lock` (`client/v3/concurrency/mutex.go`).

Users: `server/etcdserver/api/v3lock/lock.go:45` (`NewMutex(s, req.Name)`, `Lock(ctx)`, then
`Key()` and `Header()` returned to the remote client, which fences its writes on the key and
`Unlock`s by deleting it; the in-process client: each request's principal is the RPC context's),
etcdctl's `lock` command (not in the pinned sources), etcd's tests
(`tests/integration/clientv3/concurrency/mutex_test.go`, `example_mutex_test.go`: `Lock`, `TryLock`
and `ErrLocked`, `IsOwner` in a `Txn`, `Unlock`, `NewLocker`; `tests/integration/v3lock_grpc_test.go`:
a second lock's header after the first's). Snippet: `concurrency/mutex.go` (`ReqLocker`).

Proof sketch: the embedded field (`↦□`), `isSession_client`, `Client.Ctx.spec` (1c: the client's
context, `ctxPrin` of its principal `who`), `Mutex.Lock.spec`; on an error `panic(err)` (Perennial's
panic outcome).

Changes: from `specs-ref`'s `lockerMutex__Lock.lean`: as `Mutex.Lock`.

Changes: verify-round: the key is the session's (`sessKey`) and `cr` a create revision after `σ0`, as `Mutex.Lock.spec`'s.

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

/-- `l.Lock()` (`sync.Locker`): `Mutex.Lock` with the client's context; it returns with the lock fact, or panics with the error. -/
def lockerMutex.Lock.spec : Prop :=
  ∀ (lm m s c : Loc) (pfx : GoString) (st : MutexSt) (γ : Cluster) (dflt who : Principal) (id : w64)
    (T : State → State → Prop) (P : IProp GF) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ lm.[go_etcd_io.etcd.client.v3.concurrency.lockerMutex, go!"Mutex"] ↦□ m ∗ isMutex m s pfx ∗ mutexSt m st ∗
      isSession s c γ id ∗ isClient c γ dflt ∗ etcdLent γ T P ∗ P ∗ etcdLb γ σ0 ∗ ⌜effIn (mutexEff pfx (sint.Z id)) T⌝ }}
    (App (Val (lm @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.lockerMutex.ty @!! go!"Lock")) (Val #()))
  {{ (r : val), RET r;
      (⌜r = #()⌝ ∗ P ∗ ∃ (k : GoString) (cr : Nat) (hd : Loc) (hm : HeaderM) (σ : State),
          mutexSt m { key := k, rev := W64 cr, hdr := hd } ∗ etcdLb γ σ ∗
          respHeaderOwn hd DFrac.discard hm ∗
          ⌜Reach σ0 σ ∧ k = sessKey pfx (sint.Z id) ∧ lockedSince pfx k cr σ ∧ hm.revision = W64 σ.kv.rev ∧
            (σ0.kv.rev < cr ∨ ∃ r, σ0.kv.store k = some r ∧ r.createRev = cr)⌝) ∨
      (⌜∃ err : GoInterface, err ≠ GoInterface.nil ∧ r = PanicV #err⌝ ∗ ∃ st' : MutexSt, mutexSt m st') }}

end spec

end Concurrency
end EtcdGrove
end Perennial
