/-
`(*metricsTxnWrite).Changes` (promoted; `storeTxnWrite.Changes`, `txnReadWrite.Changes`).

**Users**: through `TxnRead`/`TxnWrite` values: the server's transactions (`txn/range.go:53`, `txn/txn.go:43, 67`, `txn/put.go:39`, `txn/delete.go:33`: `store.Read`/`Write` return a `*metricsTxnWrite`), the lessor's `Revoke` (`lessor.go:350, 361`, through `mvccDeleter`), the tester (`mvccrand.go:395-495, 627-647`). Snippet `ReqSoleWriter` (`txn/txn.go:97, 153`: `len(Changes()) > 0`).

**Proof sketch**: the inner slice `tw.changes` (one record per event: `put` and `delete` append one each), or `nil` for a read-only transaction; only its length is given (the records are shared with a watchable store's `End`, which writes a delete's `ModRevision`).

**Changes** from the old spec: unchanged (length only).

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

/-- `Txn.Changes`'s contract at `*metricsTxnWrite`. -/
def metricsTxnWrite.Changes.spec : Prop :=
  ∀ s : Loc, Txn.Changes.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
