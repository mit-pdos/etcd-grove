/-
`(*metricsTxnWrite).End` (`metrics_txn.go:56`): the metrics, then (deferred) the inner `End`.

**Users**: through `TxnRead`/`TxnWrite` values: the server's transactions (`txn/range.go:53`, `txn/txn.go:43, 67`, `txn/put.go:39`, `txn/delete.go:33`: `store.Read`/`Write` return a `*metricsTxnWrite`), the lessor's `Revoke` (`lessor.go:350, 361`, through `mvccDeleter`), the tester (`mvccrand.go:395-495, 627-647`). Snippets `ReqSoleWriter`, `ReqReadFloor`.

**Proof sketch**: the counters (no panic); the inner `End`: a read transaction's `storeTxnRead.End` (`RUnlock`s: the storage slot and `s.mu`'s, the token back); a write transaction's `storeTxnWrite.End`: with changes, `s.revMu.Lock()`, `currentRev++` (both of the caller's updates fire here: a store without watchers notifies at its bump), `tx.Unlock()` (`Pk` back; the batch's data visible, `kbData`), `s.revMu.Unlock()`; without, `Unlock` only (the updates fire with nothing pending: `notify []`, the commit of nothing); `s.mu.RUnlock()`.

**Changes** from `specs-ref`'s file: the two-step commit (the frozen API), no writer fragments.

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

/-- `Txn.End`'s contract at `*metricsTxnWrite`. -/
def metricsTxnWrite.End.spec : Prop :=
  ∀ s : Loc, Txn.End.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
