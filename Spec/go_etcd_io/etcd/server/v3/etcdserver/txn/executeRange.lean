/-
`executeRange` (`range.go`): a range on a transaction (`Range`'s read transaction, `Txn`'s write
transaction or read-only wrapper). Lean-first; see `InvRange.lean`, `RangeModel.lean`,
`InvTxn.lean`.
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

/-- `executeRange(ctx, lg, txnRead, r, withTotalCount)` on a transaction of either kind behind a
`*metricsTxnWrite`, or the read-only wrapper of a read transaction (`txnViewIs`): `rangeResult`
at the log and revision the transaction reads (the response of the server's selection, or
`ErrFutureRev`, or a context error); at a context never canceled (`nd`), no context error.
Premises: a valid sort target, and a small sorted selection (`sortSmall`, at the state read). -/
abbrev txn.executeRange.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg s : Loc)
    (γ : mvcc.StoreNames) (tw : GoInterface) (kind : mvcc.TxnKind) (ro : Bool) (r : Loc)
    (o : OpFull) (withTotal : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      txn.txnViewIs tw s γ kind ro ∗ context.isContext ctx cd ∗
      (if nd then mvcc.neverDone cd else iprop(True)) ∗ txn.rangeRequestIs r o ∗
      ⌜txn.validSortTarget o ∧ txn.sortSmall o (mvcc.stateAt kind.readLog
        (sint.nat (mvcc.rangeRev kind.readRev o.base.rev)))⌝ }}
    (App (App (App (App (App (Val (@! txn.executeRange)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #tw)) (Val #r)) (Val #withTotal))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      txn.txnViewIs tw s γ kind ro ∗ txn.rangeResult resp err kind.readLog kind.readRev o withTotal ∗
      ⌜nd = true → err = GoInterface.nil ∨ sint.Z kind.readRev < sint.Z o.base.rev⌝ }}

end spec

end EtcdGrove
end Perennial
