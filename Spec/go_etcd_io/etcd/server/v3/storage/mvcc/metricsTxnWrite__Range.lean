/-
`(*metricsTxnWrite).Range` (`metrics_txn.go:39`): counts the range, then the inner transaction's `Range` (a read transaction's `txnReadWrite{storeTxnRead}`, a write transaction's `storeTxnWrite`).

**Users**: through `TxnRead`/`TxnWrite` values: the server's transactions (`txn/range.go:53`, `txn/txn.go:43, 67`, `txn/put.go:39`, `txn/delete.go:33`: `store.Read`/`Write` return a `*metricsTxnWrite`), the lessor's `Revoke` (`lessor.go:350, 361`, through `mvccDeleter`), the tester (`mvccrand.go:395-495, 627-647`). Snippets `ReqReadFloor`, `ReqSoleWriter`.

**Proof sketch**: the inner `Range` (`storeTxnCommon.rangeKeys` at the transaction's revision, over `MTxn.readHist`; a full read checks the context); the counter is the wrapper's own field.

**Changes** from `specs-ref`'s `metricsTxnWrite__Range.lean`: over `rangeOut` (W0's history); the sort facts are `rangeResult`'s `kvsFit`.

**Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

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

/-- `Txn.Range`'s contract at `*metricsTxnWrite`. -/
def metricsTxnWrite.Range.spec : Prop :=
  ∀ s : Loc, Txn.Range.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
