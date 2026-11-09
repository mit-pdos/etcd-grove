/-
`(*concurrency.Mutex).Unlock(ctx)` (`client/v3/concurrency/mutex.go`).

Users: `server/etcdserver/api/v3lock/lock.go:45` (`NewMutex(s, req.Name)`, `Lock(ctx)`, then
`Key()` and `Header()` returned to the remote client, which fences its writes on the key and
`Unlock`s by deleting it), etcdctl's `lock` command (not in the pinned sources: `Lock`, the key,
`Unlock`), recipes' callers, etcd's tests (`tests/integration/clientv3/concurrency/mutex_test.go`,
`example_mutex_test.go`: `Lock`, `TryLock` and `ErrLocked`, `IsOwner` in a `Txn`, `Unlock`,
`NewLocker`). Snippet: `concurrency/mutex.go` (`ReqLockUnlock`).

Proof sketch: the fields; `strings.HasPrefix` (Perennial); `fmt.Errorf` (Perennial) on a key not
under the prefix; the KV contract's `Delete` of the key (update from `etcdPerm`, `keysEff`'s
delete): its reply at `σ'` (the key absent there), the state released; an error, unchanged.

Changes: from `specs-ref`'s `Mutex__Unlock.lean`: over the cluster's states.

Margin: the delete is not fenced: it deletes the key even if it was re-created by another
`Mutex` of the session (`issues/mutex-lock-recreated.md`'s related upstream discussion).
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

/-- `m.Unlock(ctx)`: `nil`, the key absent at a state the cluster reached, the mutex released; `ErrLockReleased` if not held; or another error, unchanged. -/
def Mutex.Unlock.spec : Prop :=
  ∀ (m s : Loc) (pfx : GoString) (st : MutexSt) (γ : Cluster) (who : Principal) (id : w64)
    (ctx : GoInterface) (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isMutex m s pfx ∗ mutexSt m st ∗ isSession s γ who id ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗
      etcdPerm γ T ∗ ⌜effIn (keysEff (fun k => pfx <+: k) (sint.Z id)) T⌝ }}
    (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Mutex.ty @!! go!"Unlock")) (Val #ctx))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ : State, etcdLb γ σ ∗ ⌜σ.kv.store st.key = none⌝ ∗
          mutexSt m st.released) ∨
      (⌜err = concErrVal .lockReleased ∧ (st.key = [] ∨ sint.Z st.rev ≤ 0 ∨ st.key = [W8 0])⌝ ∗
          mutexSt m st) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ mutexSt m st) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
