/-
`(*store).Write(trace)` (`kvstore_txn.go:174`): a write transaction.

**Users** (through `KV.Write` on a plain store, or wrapped by the watchable store's own `Write`, 3f):
`txn.Put` (`txn/put.go:39`), `txn.DeleteRange` (`txn/delete.go:33`), `txn.Txn`'s write path
(`txn/txn.go:67`), the lessor's range deleter (`server.go:1087`, `lessor.go:343`: `mvccDeleter`), the
tester's writer (`mvccrand.go:419, 438, 488`). Snippets `ReqSoleWriter`, `ReqPutRev`,
`ReqDeleteRange`, `ReqRangeDeleter` (`examples/specreq/mvcc/{store,lease}.go`).

**Proof sketch**: `s.mu.RLock()` (the reader token's slot); `s.b.BatchTx()`, `LockInsideApply()`
(`keyBackend`: on the reader token's part of the open share `kbOpen`, the hook from `Pre` to `Q` under
`Pk`, `kbLocked B q D D` and the session's liveness; `B` the store's by
`mvccBackend`'s agreement); with the batch lock held no other writer, compaction or restore runs, so
the store's invariant's state `σ` is fixed (nothing pending: a watchable store's `End` finishes both
steps under the lock); fire the caller's update at `σ` where `beginRev := s.currentRev` is read (the
invariant's `currentRev = σ.rev`); `newMetricsTxnWrite` of the `storeTxnWrite` (`storeTxnW`).
`mvccTxn t γ trace (.write σ [])` keeps `kbLocked`, the read slot and the token until `End`.

**Changes** from `specs-ref`'s `store__Write.lean`: the contract at `*store` (the frozen API's), no
writer fragments, revision tokens or certificate maps; the state is the client's.

**Margin**: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `KV.Write`'s contract at `*store`. -/
def store.Write.spec : Prop :=
  ∀ s : Loc, KV.Write.contract (GF := GF) (go.GoType.PointerType store.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
