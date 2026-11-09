/-
`(*metricsTxnWrite).Put` (`metrics_txn.go:49`).

**Users**: through `TxnRead`/`TxnWrite` values: the server's transactions (`txn/range.go:53`, `txn/txn.go:43, 67`, `txn/put.go:39`, `txn/delete.go:33`: `store.Read`/`Write` return a `*metricsTxnWrite`), the lessor's `Revoke` (`lessor.go:350, 361`, through `mvccDeleter`), the tester (`mvccrand.go:395-495, 627-647`). Snippets `ReqPutRev`, `ReqPutLease`.

**Proof sketch**: count and size, then `storeTxnWrite.Put` (`put`: the index's `Get` for the creation revision and version, `GetLease`, `UnsafeSeqPut`, the index's `Put`, `Detach`/`Attach` on 3c's writer token (`lessor.Detach.spec`, `.Attach.spec`: `putLs`); `Attach` of a live lease succeeds, else it panics, hence `lid = 0 ∨ ls.leases lid ≠ none`; a `Detach` of a lease not live changes nothing).

**Changes** from `specs-ref`'s file: the event `putEv` over W0's records; the old key-length bound of `Attach` dropped (the lessor's internal invariant, 3c's).

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

/-- `Txn.Put`'s contract at `*metricsTxnWrite`. -/
def metricsTxnWrite.Put.spec : Prop :=
  ∀ s : Loc, Txn.Put.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
