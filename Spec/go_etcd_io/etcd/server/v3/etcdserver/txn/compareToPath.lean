/-
`compareToPath` (`txn.go`). Lean-first; see `TxnRun.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvTxn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `compareToPath(rv, rt)` on a read transaction (of the committed log `log`): the path
`txnPath` (the verdicts of the transaction's and its chosen nested transactions' comparisons, in
pre-order, all at the state after `log`), a fresh slice. -/
abbrev txn.compareToPath.spec : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) (rt : Loc) (t : TxnModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ mvcc.isTxnRead mw s γ log rev ∗ txn.txnRequestIs rt t }}
    (App (App (Val (@! txn.compareToPath))
      (Val #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface))) (Val #rt))
  {{ (sl : GoSlice), RET #sl; mvcc.isTxnRead mw s γ log rev ∗
      sl ↦* txn.txnPath (mvcc.stateAfter log) t ∗ ownSliceCap Bool sl (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
