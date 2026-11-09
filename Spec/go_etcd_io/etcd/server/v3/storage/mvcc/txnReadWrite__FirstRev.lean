/-
`(*txnReadWrite).FirstRev` (promoted).

**Users**: `txn.Txn`'s read-only path (`txn/txn.go:69`: `NewReadOnlyTxnWrite(txnRead)`, then `txn`/`executeTxn`/`checkTxn` call the `TxnWrite` methods), the tester's readers (`mvccrand.go:475-483, 626-634`). Snippet `ReqReadOnlyTxn`.

**Proof sketch**: the inner read transaction's `FirstRev` (`σ.crev`).

**Changes** from `specs-ref`'s `txnReadWrite__FirstRev.lean`: the contract at `*txnReadWrite` (the frozen
API's canonical spec).

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

/-- `Txn.FirstRev`'s contract at `*txnReadWrite`. -/
def txnReadWrite.FirstRev.spec : Prop :=
  ∀ s : Loc, Txn.FirstRev.contract (GF := GF) (go.GoType.PointerType txnReadWrite.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
