/-
`(*concurrency.Mutex).TryLock(ctx)` (`client/v3/concurrency/mutex.go`).

Users: `server/etcdserver/api/v3lock/lock.go:45` (`NewMutex(s, req.Name)`, `Lock(ctx)`, then
`Key()` and `Header()` returned to the remote client, which fences its writes on the key and
`Unlock`s by deleting it), etcdctl's `lock` command (not in the pinned sources: `Lock`, the key,
`Unlock`), recipes' callers, etcd's tests (`tests/integration/clientv3/concurrency/mutex_test.go`,
`example_mutex_test.go`: `Lock`, `TryLock` and `ErrLocked`, `IsOwner` in a `Txn`, `Unlock`,
`NewLocker`). Snippet: `concurrency/mutex.go` (`ReqTryLock`).

Proof sketch: `Mutex.tryAcquire.spec`; the second response's key-values (`firstCreate`): none or
the oldest's create revision is `c`: the key holds at the transaction's state (`holdsAt`), the
header kept (persisted: `replyPersist`); otherwise an older key holds there, and the key is
deleted (`isClient_KV`, the KV contract's `Delete`, the update from `etcdPerm`: `keysEff`'s
delete), `ErrLocked` (`init.spec`).

Changes: from `specs-ref`'s `Mutex__TryLock.lean`: over the cluster's states; `ErrLocked` also says
the key is gone and another key held the lock.

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

/-- `m.TryLock(ctx)`: `nil` and the key holds at a state the cluster reached (the header kept is that state's); or `ErrLocked`, an older key held the lock and the mutex's key was deleted (released); or another error. -/
def Mutex.TryLock.spec : Prop :=
  ∀ (m s : Loc) (pfx : GoString) (st : MutexSt) (γ : Cluster) (who : Principal) (id : w64)
    (ctx : GoInterface) (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isMutex m s pfx ∗ mutexSt m st ∗ isSession s γ who id ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗
      etcdPerm γ T ∗ ⌜effIn (keysEff (fun k => pfx <+: k) (sint.Z id)) T⌝ }}
    (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Mutex.ty @!! go!"TryLock")) (Val #ctx))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ (k : GoString) (c : Nat) (hd : Loc) (hm : HeaderM) (σ : State),
          mutexSt m { key := k, rev := W64 c, hdr := hd } ∗ etcdLb γ σ ∗
          respHeaderOwn hd DFrac.discard hm ∗
          ⌜0 < c ∧ c ≤ σ.kv.rev ∧ holdsAt pfx k c σ.kv.store ∧ hm.revision = W64 σ.kv.rev⌝) ∨
      (⌜err = concErrVal .locked⌝ ∗ ∃ (k : GoString) (c : Nat) (σ σ' : State),
          mutexSt m { key := [W8 0], rev := W64 (-1), hdr := st.hdr } ∗ etcdLb γ σ ∗ etcdLb γ σ' ∗
          ⌜pfx <+: k ∧ (∃ r, σ.kv.store k = some r ∧ r.createRev = c) ∧
            ¬ noOlder pfx c σ.kv.store ∧ σ'.kv.store k = none⌝) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ∃ st' : MutexSt, mutexSt m st') }}

end spec

end Concurrency
end EtcdGrove
end Perennial
