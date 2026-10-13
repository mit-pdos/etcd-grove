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

/-- **A transaction's response after a failed run** (read-only; `txn`'s error outcome): not
nil, its header and the header's revision, its `Responses` slice (what `Txn` reads for its
trace). -/
def txn.txnRespShell (resp : Loc) : IProp GF :=
  iprop(⌜resp ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (rev : w64),
    structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ h ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rev ∗
    structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ sl)

instance txn.txnRespShell_persistent (resp : Loc) :
    Persistent (txn.txnRespShell (GF := GF) resp) := by
  unfold txn.txnRespShell; infer_instance

set_option linter.iris.dupNamespace false in
/-- `txn(ctx, lg, txnWrite, rt, isWrite, txnPath, skip)` on a fresh write transaction of the
committed log `ilog` (`isWrite`), or the read-only wrapper of a read transaction of `ilog`, the
path `txnPath` of `rt` at the state after `ilog`: the server's transaction (`srvRunTxn`) at the
pending revision, its changes pending, the response with header revision the transaction's
(`writeRev`: the committed log's last revision, plus one if it changed something), the header's
id fields owned (`respHdrOwn`); `nil` (the panicking branch is not reached). Premises:
`executeTxn`'s. At a context that may be done (`nd = false`, only for the read-only wrapper, with
a logger; 2026-10-12, the request path's unit 3b): or `executeTxn`'s context error
(`mvcc.errorfIs`), logged (`lg.Error`), and the partly filled response (`txnRespShell`). -/
abbrev txn.txn.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg s : Loc)
    (γ : mvcc.StoreNames) (tw : GoInterface) (ro : Bool) (ilog : mvcc.Log) (rt : Loc)
    (t : TxnModel) (pl : GoSlice) (skip : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txn.txnWriteIs tw s γ ro ilog [] ∗ mvcc.txnCtx ctx cd ∗
      (if nd then mvcc.neverDone cd else iprop(True)) ∗
      txn.txnRequestIs rt t ∗ pl ↦*□ txn.txnPath (mvcc.stateAfter ilog) t ∗
      txn.leasesOk γ.leases (txn.opsLeases (mvcc.stateAfter ilog)
        (t.branch (txn.txnOk (mvcc.stateAfter ilog) t))) ∗
      (if ro then iprop(True) else txn.leasesKnown γ.leases (mvcc.stateAfter ilog)) ∗
      ⌜txn.OpsOk false (mvcc.stateAfter ilog) (W64 (ilog.length : Int)) (mvcc.stateAfter ilog)
          (t.branch (txn.txnOk (mvcc.stateAfter ilog) t)) ∧
        (txn.srvRunTxn (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) t).2.1.length < mvcc.putMax γ ∧
        (ro = true → txn.txnReadonly t = true) ∧ (nd = false → ro = true ∧ lg ≠ null)⌝ }}
    (App (App (App (App (App (App (App (Val (@! txn.txn)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #tw)) (Val #rt)) (Val #(!ro))) (Val #pl)) (Val #skip))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗
        txn.txnWriteIs tw s γ ro ilog
          (txn.srvRunTxn (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) t).2.1 ∗
        txn.txnResponseIs skip resp
          (W64 (mvcc.writeRev ilog (txn.srvRunTxn (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) t).2.1
            : Int)) t
          (txn.srvRunTxn (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) t).1
          (txn.srvRunTxn (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) t).2.2 ∗
        txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp) ∗
        (if ro then iprop(True) else
          txn.leasesKnown γ.leases (mvcc.applyChanges (W64 (ilog.length : Int)) (mvcc.stateAfter ilog)
            (txn.srvRunTxn (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) t).2.1))) ∨
      (⌜nd = false⌝ ∗ mvcc.errorfIs err ∗
        (∃ pend' : List mvcc.Change, txn.txnWriteIs tw s γ ro ilog pend') ∗
        txn.txnRespShell resp) }}

end spec

end EtcdGrove
end Perennial
