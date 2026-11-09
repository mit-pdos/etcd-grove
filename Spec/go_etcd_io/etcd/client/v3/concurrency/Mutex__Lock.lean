/-
`(*concurrency.Mutex).Lock(ctx)` (`client/v3/concurrency/mutex.go`).

Users: `server/etcdserver/api/v3lock/lock.go:45` (`NewMutex(s, req.Name)`, `Lock(ctx)`, then
`Key()` and `Header()` returned to the remote client, which fences its writes on the key and
`Unlock`s by deleting it; the in-process client: each request's principal is the RPC context's),
etcdctl's `lock` command (not in the pinned sources), etcd's tests
(`tests/integration/clientv3/concurrency/mutex_test.go`, `example_mutex_test.go`: `Lock`, `TryLock`
and `ErrLocked`, `IsOwner` in a `Txn`, `Unlock`, `NewLocker`; `tests/integration/v3lock_grpc_test.go`:
a second lock's header after the first's). Snippets: `concurrency/mutex.go` (`ReqFencedWrite`, `ReqV3LockPattern`,
`ReqLockUnlock`, `ReqLockAfterUnlock`).

Proof sketch: `Mutex.tryAcquire.spec` (the key `k`, its create revision `c`). If the oldest key's
create revision is `c` (or none: impossible, `k` is there), the transaction's state gives
`lockedSince` (`holdsAt` at it), the header kept. Otherwise `waitDeletes.spec` with `c - 1`
(positive: `c ≥ 2`, `etcdLb_init`): at a state `σw` no key under the prefix is older than `c`;
on its error `Unlock(client.Ctx())` (`Client.Ctx.spec`, 1c, over `clientBase c dflt` from `isClient`:
`ctxPrin dflt ctx dflt`, the client's own principal; `Mutex.Unlock.spec` with `mutexEff`'s delete) and the error. Then the KV contract's `Get(ctx,
k)` (a linearizable read, its update from `etcdPeek`) at `σ`, after `σw` (`etcdLb_reach` inside the
update): no key is created older than `c` after `σw` (their create revisions are later revisions),
so `noOlder pfx c` still holds at `σ`; `k` present there: `lockedSince pfx k c σ`, the header kept
(persisted) has `σ`'s revision; absent: `ErrSessionExpired`; an error: `Unlock` and the error.
The lent permission (`etcdLent γ T P` with the token `P`): each write's exclusive update
is built from it (giving `P` up, back at the commit), each read's from its `etcdPeek`; the first
firing after the call starts gives `Reach σ0` (`etcdLb_reach`). `P` is returned on every outcome
whose writes have all been answered; an error after which a write may be pending keeps it.

Changes: from `specs-ref`'s `Mutex__Lock.lean`: over the cluster's states; the old disjunction
`lockedAt ∨ keyRecreated` is one fact, `lockedSince` (the key present with a create revision at
least `c`, nothing older than `c`), whose use is the fence (`fence`): a write guarded by
`IsOwner()` succeeds only where the key holds, whether or not it was re-created
(`issues/mutex-lock-recreated.md`). Any context (`ctxOk`), not only a cancelable Perennial one.
Round 1: the lent permission (`P` back on `nil` and `ErrSessionExpired`), the result after `σ0`, the
principal per call (`isClient c γ dflt`, `ctxPrin dflt ctx who`).

Margin: with the upstream fix of `issues/mutex-lock-recreated.md` the key's create revision would
be exactly `c` (`holdsAt` at `σ`). The errors are not classified (any client error, a watch's,
the context's, `lost watcher`); the mutex's state after one is any (its key may have been
deleted by the cleanup `Unlock`, which runs as the client's own principal:
`nonissues/etcd-v3lock-auth-cleanup-unauthenticated.md`).
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

/-- `m.Lock(ctx)`: `nil` and the lock fact at a state the cluster reached after `σ0` (the header kept is that state's), so that writes fenced by `IsOwner()` take effect only while the key holds; `ErrSessionExpired` with the key absent; or another error. -/
def Mutex.Lock.spec : Prop :=
  ∀ (m s c : Loc) (pfx : GoString) (st : MutexSt) (γ : Cluster) (dflt who : Principal) (id : w64)
    (ctx : GoInterface) (T : State → State → Prop) (P : IProp GF) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isMutex m s pfx ∗ mutexSt m st ∗ isSession s c γ id ∗ isClient c γ dflt ∗
      Context.ctxOk ctx ∗ ctxPrin dflt ctx who ∗ etcdLent γ T P ∗ P ∗ etcdLb γ σ0 ∗ ⌜effIn (mutexEff pfx (sint.Z id)) T⌝ }}
    (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Mutex.ty @!! go!"Lock")) (Val #ctx))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ P ∗ ∃ (k : GoString) (cr : Nat) (hd : Loc) (hm : HeaderM) (σ : State),
          mutexSt m { key := k, rev := W64 cr, hdr := hd } ∗ etcdLb γ σ ∗
          respHeaderOwn hd DFrac.discard hm ∗
          ⌜Reach σ0 σ ∧ lockedSince pfx k cr σ ∧ hm.revision = W64 σ.kv.rev⌝) ∨
      (⌜err = concErrVal .sessionExpired⌝ ∗ P ∗ ∃ (st' : MutexSt) (σ : State), mutexSt m st' ∗
          etcdLb γ σ ∗ ⌜Reach σ0 σ ∧ pfx <+: st'.key ∧ σ.kv.store st'.key = none⌝) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ∃ st' : MutexSt, mutexSt m st') }}

end spec

end Concurrency
end EtcdGrove
end Perennial
