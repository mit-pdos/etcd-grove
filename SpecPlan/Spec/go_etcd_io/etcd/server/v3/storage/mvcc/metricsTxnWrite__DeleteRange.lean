/-
`(*metricsTxnWrite).DeleteRange` (`metrics_txn.go:44`).

**Users**: through `TxnRead`/`TxnWrite` values: the server's transactions (`txn/range.go:53`, `txn/txn.go:43, 67`, `txn/put.go:39`, `txn/delete.go:33`: `store.Read`/`Write` return a `*metricsTxnWrite`), the lessor's `Revoke` (`lessor.go:350, 361`, through `mvccDeleter`), the tester (`mvccrand.go:395-495, 627-647`). Snippets `ReqDeleteRange`, `ReqRangeDeleter`.

**Proof sketch**: count, then `storeTxnWrite.DeleteRange` (a `.write` transaction: `deleteRange` reads the index at the transaction's revision; `delete` per key: an `UnsafeSeqPut` of the tombstone, the index's `Tombstone`, the lessor's `GetLease`/`Detach` on 3c's writer token: `delsLs`).

**Changes** from `specs-ref`'s file: over W0's events (`ds.map .delete`), the lessor's items provisional (3c's).

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

/-- `Txn.DeleteRange`'s contract at `*metricsTxnWrite`. -/
def metricsTxnWrite.DeleteRange.spec : Prop :=
  ∀ s : Loc, Txn.DeleteRange.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
