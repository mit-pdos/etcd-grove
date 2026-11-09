/-
`(*watchableStore).Write(trace)` (`watchable_store_txn.go`): a write transaction whose `End` notifies
the watchers: the `KV` interface's `Write` contract (3e's `KV.Write.contract`) at the watchable store.

**Users.** The apply path (`etcdserver/txn`, 2d: puts, deletes, transactions through `kv.Write`), the
lessor's range deleter (`watchable_store.go:107`: `s.Write(traceutil.TODO())`, 3c's revoke), the
store's write view (`kv_view.go:47, 53`). Snippet: `mvccwatch/store.go` `ReqStoreWrites`.

**Proof sketch.** `s.store.Write(trace)` (3e's `store.Write` spec: the inner transaction, its update
fired, the hook run), wrapped with `s` as a `*watchableStoreTxnWrite`, whose `mvccTxn` is the inner
one's with the watchable store's invariant (`watchableAt`) for `End`'s notification.

**Changes** from `specs-ref`'s file: the canonical instance of 3e's restated contract.

**Margin.** As the contract's.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.Write` meets `KV.Write`'s contract. -/
def watchableStore.Write.spec : Prop := ∀ s : Loc, KV.Write.contract (GF := GF) (go.GoType.PointerType watchableStore.ty) #s

end spec

end Mvcc
end EtcdGrove
end Perennial
