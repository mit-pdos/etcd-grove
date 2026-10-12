/-
`executeRange` (`range.go`): a range on a read transaction.
Lean-first; see `InvRange.lean`, `RangeModel.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvRange

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

/-- `executeRange(ctx, lg, txnRead, r, withTotalCount)` on a read transaction (the `mvcc.TxnRead`
whose dynamic type is `*metricsTxnWrite`, of the committed log `log` at revision `rev`):
`rangeResult` (the response of the server's selection, or `ErrFutureRev`, or a context error).
Premises: a valid sort target, and the sort's premise on the log (`sortOk`). -/
abbrev txn.executeRange.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg mw s : Loc)
    (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) (r : Loc) (o : OpFull) (withTotal : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      mvcc.isTxnRead mw s γ log rev ∗ context.isContext ctx cd ∗ txn.rangeRequestIs r o ∗
      ⌜txn.validSortTarget o ∧ txn.sortOk o log⌝ }}
    (App (App (App (App (App (Val (@! txn.executeRange)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw : GoInterface)))
      (Val #r)) (Val #withTotal))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      mvcc.isTxnRead mw s γ log rev ∗ txn.rangeResult resp err log rev o withTotal }}

end spec

end EtcdGrove
end Perennial
