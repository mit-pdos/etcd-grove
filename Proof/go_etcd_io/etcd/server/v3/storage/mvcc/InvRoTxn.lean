/-
The read-only write transaction (`kv.go`: `NewReadOnlyTxnWrite`, `txnReadWrite`), for the
server's `txn` package: `Txn` wraps a read-only transaction's `TxnRead` as a `TxnWrite`.
Lean-first; additive (the read transaction's predicates are `InvStore.lean`'s, unchanged).

`isRoTxnWrite trw s γ log rev`: the `txnReadWrite` at `trw` (its `TxnRead` field, owned) wraps
the read transaction `store.Read` returned (`isTxnRead`: a `*metricsTxnWrite`), of the
committed log `log` at revision `rev`. Its `FirstRev`, `Rev`, `Range` and `End` are the read
transaction's (promoted from the embedded interface), `Changes` returns `nil`, `Put` and
`DeleteRange` panic.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The `txnReadWrite` at `trw` wraps a read transaction of `log` at `rev`. -/
def isRoTxnWrite (trw s : Loc) (γ : StoreNames) (log : Log) (rev : w64) : IProp GF :=
  iprop(∃ mw : Loc,
    trw.[txnReadWrite, go!"TxnRead"] ↦
      (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface) ∗
    isTxnRead mw s γ log rev)

end defs

end mvcc
end EtcdGrove
end Perennial
