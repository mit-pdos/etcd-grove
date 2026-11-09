/-
`(*metricsTxnWrite).Rev` (promoted; `storeTxnCommon.Rev`, `storeTxnWrite.Rev`).

**Users**: through `TxnRead`/`TxnWrite` values: the server's transactions (`txn/range.go:53`, `txn/txn.go:43, 67`, `txn/put.go:39`, `txn/delete.go:33`: `store.Read`/`Write` return a `*metricsTxnWrite`), the lessor's `Revoke` (`lessor.go:350, 361`, through `mvccDeleter`), the tester (`mvccrand.go:395-495, 627-647`). Snippets `ReqSoleWriter`, `ReqReadFloor` (`txn/txn.go:96, 152`).

**Proof sketch**: a read transaction's `rev` (`currentRev` at `Read`), a write transaction's `beginRev`: both `σ.rev`.

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

/-- `Txn.Rev`'s contract at `*metricsTxnWrite`. -/
def metricsTxnWrite.Rev.spec : Prop :=
  ∀ s : Loc, Txn.Rev.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
