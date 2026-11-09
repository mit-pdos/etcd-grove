/-
`(*concurrency.lockerMutex).Lock` (`client/v3/concurrency/mutex.go`).

Users: `server/etcdserver/api/v3lock/lock.go:45` (`NewMutex(s, req.Name)`, `Lock(ctx)`, then
`Key()` and `Header()` returned to the remote client, which fences its writes on the key and
`Unlock`s by deleting it), etcdctl's `lock` command (not in the pinned sources: `Lock`, the key,
`Unlock`), recipes' callers, etcd's tests (`tests/integration/clientv3/concurrency/mutex_test.go`,
`example_mutex_test.go`: `Lock`, `TryLock` and `ErrLocked`, `IsOwner` in a `Txn`, `Unlock`,
`NewLocker`). Snippet: `concurrency/mutex.go` (`ReqLocker`).

Proof sketch: the embedded field (`↦□`), `isSession_client`, `Client.Ctx.spec` (1c: `ctxOk`),
`Mutex.Lock.spec`; on an error `panic(err)` (Perennial's panic outcome).

Changes: from `specs-ref`'s `lockerMutex__Lock.lean`: as `Mutex.Lock`.

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
  ∀ (lm m s : Loc) (pfx : GoString) (st : MutexSt) (γ : Cluster) (who : Principal) (id : w64)
    (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ lm.[go_etcd_io.etcd.client.v3.concurrency.lockerMutex, go!"Mutex"] ↦□ m ∗ isMutex m s pfx ∗ mutexSt m st ∗
      isSession s γ who id ∗ etcdPerm γ T ∗ ⌜effIn (keysEff (fun k => pfx <+: k) (sint.Z id)) T⌝ }}
    (App (Val (lm @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.lockerMutex.ty @!! go!"Lock")) (Val #()))
  {{ (r : val), RET r;
      (⌜r = #()⌝ ∗ ∃ (k : GoString) (c : Nat) (hd : Loc) (hm : HeaderM) (σ : State),
          mutexSt m { key := k, rev := W64 c, hdr := hd } ∗ etcdLb γ σ ∗
          respHeaderOwn hd DFrac.discard hm ∗ ⌜lockedSince pfx k c σ ∧ hm.revision = W64 σ.kv.rev⌝) ∨
      (⌜∃ err : GoInterface, err ≠ GoInterface.nil ∧ r = PanicV #err⌝ ∗ ∃ st' : MutexSt, mutexSt m st') }}

end spec

end Concurrency
end EtcdGrove
end Perennial
