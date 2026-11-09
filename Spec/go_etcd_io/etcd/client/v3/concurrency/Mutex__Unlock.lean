/-
`(*concurrency.Mutex).Unlock(ctx)` (`client/v3/concurrency/mutex.go`).

Users: `server/etcdserver/api/v3lock/lock.go:45` (`NewMutex(s, req.Name)`, `Lock(ctx)`, then
`Key()` and `Header()` returned to the remote client, which fences its writes on the key and
`Unlock`s by deleting it; the in-process client: each request's principal is the RPC context's),
etcdctl's `lock` command (not in the pinned sources), etcd's tests
(`tests/integration/clientv3/concurrency/mutex_test.go`, `example_mutex_test.go`: `Lock`, `TryLock`
and `ErrLocked`, `IsOwner` in a `Txn`, `Unlock`, `NewLocker`; `tests/integration/v3lock_grpc_test.go`:
a second lock's header after the first's). Snippet: `concurrency/mutex.go` (`ReqLockUnlock`).

Proof sketch: the fields; `strings.HasPrefix` (Perennial); `fmt.Errorf` (Perennial) on a key not
under the prefix; the KV contract's `Delete` of the key (update from the lent permission: the
delete of the key): its reply at `σ'` (the key absent there), the state released; an error,
unchanged. The lent permission (`etcdLent γ T P` with the token `P`): each write's exclusive update
is built from it (giving `P` up, back at the commit), each read's from its `etcdPeek`; the first
firing after the call starts gives `Reach σ0` (`etcdLb_reach`). `P` is returned on every outcome
whose writes have all been answered; an error after which a write may be pending keeps it.

Changes: from `specs-ref`'s `Mutex__Unlock.lean`: over the cluster's states. Round 1: the effect
is the delete of the mutex's key only; the lent permission; `σ0`.

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

/-- `m.Unlock(ctx)`: `nil`, the key absent at a state the cluster reached after `σ0`, the mutex released; `ErrLockReleased` if not held; or another error, unchanged. -/
def Mutex.Unlock.spec : Prop :=
  ∀ (m s c : Loc) (pfx : GoString) (st : MutexSt) (γ : Cluster) (who : Principal) (id : w64)
    (ctx : GoInterface) (T : State → State → Prop) (P : IProp GF) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isMutex m s pfx ∗ mutexSt m st ∗ isSession s c γ id ∗ isClient c γ who ∗
      Context.ctxOk ctx ∗ ctxPrin ctx who ∗ etcdLent γ T P ∗ P ∗ etcdLb γ σ0 ∗ ⌜effIn (delEff (fun k => k = st.key ∧ pfx <+: k)) T⌝ }}
    (App (Val (m @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Mutex.ty @!! go!"Unlock")) (Val #ctx))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ P ∗ ∃ σ : State, etcdLb γ σ ∗
          ⌜Reach σ0 σ ∧ σ.kv.store st.key = none⌝ ∗ mutexSt m st.released) ∨
      (⌜err = concErrVal .lockReleased ∧ (st.key = [] ∨ sint.Z st.rev ≤ 0 ∨ st.key = [W8 0])⌝ ∗
          P ∗ mutexSt m st) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ mutexSt m st) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
