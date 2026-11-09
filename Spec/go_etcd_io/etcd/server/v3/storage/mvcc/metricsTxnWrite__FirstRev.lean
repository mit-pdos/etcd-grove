/-
`(*metricsTxnWrite).FirstRev` (promoted from the embedded `TxnWrite`; `storeTxnCommon.FirstRev`, `kvstore_txn.go:66`).

**Users**: through `TxnRead`/`TxnWrite` values: the server's transactions (`txn/range.go:53`, `txn/txn.go:43, 67`, `txn/put.go:39`, `txn/delete.go:33`: `store.Read`/`Write` return a `*metricsTxnWrite`), the lessor's `Revoke` (`lessor.go:350, 361`, through `mvccDeleter`), the tester (`mvccrand.go:395-495, 627-647`). Snippet `ReqReadFloor` (`txn/range.go:180`'s check).

**Proof sketch**: the inner `firstRev`: the compaction revision read at `Read` (a write transaction's `0`: `store.Write` sets none).

**Changes** from the old spec: unchanged in substance.

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

/-- `Txn.FirstRev`'s contract at `*metricsTxnWrite`. -/
def metricsTxnWrite.FirstRev.spec : Prop :=
  ∀ s : Loc, Txn.FirstRev.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
