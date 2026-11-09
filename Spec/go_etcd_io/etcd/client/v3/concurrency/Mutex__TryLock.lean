/-
`(*concurrency.Mutex).TryLock(ctx)` (`client/v3/concurrency/mutex.go`).

Users: `server/etcdserver/api/v3lock/lock.go:45` (`NewMutex(s, req.Name)`, `Lock(ctx)`, then
`Key()` and `Header()` returned to the remote client, which fences its writes on the key and
`Unlock`s by deleting it; the in-process client: each request's principal is the RPC context's),
etcdctl's `lock` command (not in the pinned sources), etcd's tests
(`tests/integration/clientv3/concurrency/mutex_test.go`, `example_mutex_test.go`: `Lock`, `TryLock`
and `ErrLocked`, `IsOwner` in a `Txn`, `Unlock`, `NewLocker`; `tests/integration/v3lock_grpc_test.go`:
a second lock's header after the first's). Snippet: `concurrency/mutex.go` (`ReqTryLock`).

Proof sketch: `Mutex.tryAcquire.spec`; the second response's key-values (`firstCreate`): none or
the oldest's create revision is `c`: the key holds at the transaction's state (`holdsAt`), the
header kept (persisted: `replyPersist`); otherwise an older key holds there, and the key is
deleted (`isClient_KV`, the KV contract's `Delete`, the update from the lent permission:
`mutexEff`'s delete), `ErrLocked` (`init.spec`). Every other error is a client call's: not one of
the package's values (`notConcErr`: `init.spec`'s `concErrsOk` with W0's `callErr_errorsNew`). The lent permission (`etcdLent γ T P` with the token `P`): each write's exclusive update
is built from it (giving `P` up, back at the commit), each read's from its `etcdPeek`; the first
firing after the call starts gives `Reach σ0` (`etcdLb_reach`). `P` is returned on every outcome
whose writes have all been answered; an error after which a write may be pending keeps it.

Changes: from `specs-ref`'s `Mutex__TryLock.lean`: over the cluster's states; `ErrLocked` also says
the key is gone and another key held the lock. Round 1: the lent permission, `σ0`, the other
errors distinct from the package's.

Changes: verify-round: the key held is the session's (`sessKey`, A3 completeness F2); `ErrLocked` the value its variable holds, the other errors `notConcErr` (A3 F4).

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

/-- `m.TryLock(ctx)`: `nil` and the key holds at a state the cluster reached after `σ0` (the header kept is that state's); or `ErrLocked`, an older key held the lock and the mutex's key was deleted (released); or another error, none of the package's. -/
def Mutex.TryLock.spec : Prop :=
  ∀ (m s c : Loc) (pfx : GoString) (st : MutexSt) (γ : Cluster) (dflt who : Principal) (id : w64)
    (ctx : GoInterface) (T : State → State → Prop) (P : IProp GF) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isMutex m s pfx ∗ mutexSt m st ∗ isSession s c γ id ∗ isClient c γ dflt ∗
      Context.ctxOk ctx ∗ ctxPrin dflt ctx who ∗ etcdLent γ T P ∗ P ∗ etcdLb γ σ0 ∗ ⌜effIn (mutexEff pfx (sint.Z id)) T⌝ }}
    (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Mutex.ty @!! go!"TryLock")) (Val #ctx))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ P ∗ ∃ (k : GoString) (cr : Nat) (hd : Loc) (hm : HeaderM) (σ : State),
          mutexSt m { key := k, rev := W64 cr, hdr := hd } ∗ etcdLb γ σ ∗
          respHeaderOwn hd DFrac.discard hm ∗
          ⌜Reach σ0 σ ∧ k = sessKey pfx (sint.Z id) ∧ 0 < cr ∧ cr ≤ σ.kv.rev ∧ holdsAt pfx k cr σ.kv.store ∧
            hm.revision = W64 σ.kv.rev⌝) ∨
      (globalAddr go_etcd_io.etcd.client.v3.concurrency.ErrLocked ↦□ err ∗ P ∗ ∃ (k : GoString) (cr : Nat) (σ σ' : State),
          mutexSt m { key := [W8 0], rev := W64 (-1), hdr := st.hdr } ∗ etcdLb γ σ ∗ etcdLb γ σ' ∗
          ⌜Reach σ0 σ ∧ Reach σ σ' ∧ pfx <+: k ∧ (∃ r, σ.kv.store k = some r ∧ r.createRev = cr) ∧
            ¬ noOlder pfx cr σ.kv.store ∧ σ'.kv.store k = none⌝) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ notConcErr err ∗ ∃ st' : MutexSt, mutexSt m st') }}

end spec

end Concurrency
end EtcdGrove
end Perennial
