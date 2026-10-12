/-
`txn` (`txn.go`). Lean-first; see `TxnRun.lean`, `InvTxn.lean`.
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

set_option linter.iris.dupNamespace false in
/-- `txn(ctx, lg, txnWrite, rt, isWrite, txnPath, skip)` on a fresh write transaction of the
committed log `ilog` (`isWrite`), or the read-only wrapper of a read transaction of `ilog`, the
path `txnPath` of `rt` at the state after `ilog`, at a context never canceled: the server's
transaction (`srvRunTxn`) at the pending revision, its changes pending, the response with header
revision the transaction's (`writeRev`: the committed log's last revision, plus one if it
changed something); `nil` (the panicking and logging branches are not reached). Premises:
`executeTxn`'s. -/
abbrev txn.txn.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (lg s : Loc)
    (γ : mvcc.StoreNames) (tw : GoInterface) (ro : Bool) (ilog : mvcc.Log) (rt : Loc)
    (t : TxnModel) (pl : GoSlice) (skip : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txn.txnWriteIs tw s γ ro ilog [] ∗ context.isContext ctx cd ∗ mvcc.neverDone cd ∗
      txn.txnRequestIs rt t ∗ pl ↦*□ txn.txnPath (mvcc.stateAfter ilog) t ∗
      txn.leasesOk γ.leases (txn.opsLeases (mvcc.stateAfter ilog)
        (t.branch (txn.txnOk (mvcc.stateAfter ilog) t))) ∗
      txn.leasesKnown γ.leases (mvcc.stateAfter ilog) ∗
      ⌜txn.OpsOk false (mvcc.stateAfter ilog) (W64 (ilog.length : Int)) (mvcc.stateAfter ilog)
          (t.branch (txn.txnOk (mvcc.stateAfter ilog) t)) ∧
        (txn.srvRunTxn (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) t).2.1.length < 2 ^ 63 ∧
        (ro = true → txn.txnReadonly t = true)⌝ }}
    (App (App (App (App (App (App (App (Val (@! txn.txn)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #tw)) (Val #rt)) (Val #(!ro))) (Val #pl)) (Val #skip))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ⌜err = GoInterface.nil⌝ ∗
      txn.txnWriteIs tw s γ ro ilog
        (txn.srvRunTxn (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) t).2.1 ∗
      txn.txnResponseIs skip resp
        (W64 (mvcc.writeRev ilog (txn.srvRunTxn (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) t).2.1
          : Int)) t
        (txn.srvRunTxn (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) t).1
        (txn.srvRunTxn (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) t).2.2 ∗
      txn.leasesKnown γ.leases (mvcc.applyChanges (W64 (ilog.length : Int)) (mvcc.stateAfter ilog)
        (txn.srvRunTxn (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) t).2.1) }}

end spec

end EtcdGrove
end Perennial
