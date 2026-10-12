/-
`executeTxn` (`txn.go`). Lean-first; see `TxnRun.lean`, `InvTxn.lean`.
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

/-- `executeTxn(ctx, lg, txnWrite, rt, txnPath, tresp, skip)` on a write transaction (committed
log `ilog`, `pend` pending), or (`ro`) the read-only wrapper of a read transaction of `ilog`
(nothing pending, only ranges), the path `txnPath` of `rt` at the state `s0` after `ilog` (and
anything after it), `tresp`'s `Responses` the skeleton of the chosen branch, at a context never
canceled: the server's run of the branch (`srvOps`, the nested branches by the path) at the
pending revision on the state after `pend`, its changes pending, its responses filled in
(`respsIs`; `skip`: ranges header-only); `nil` and the number of nested transactions. Premises:
the run's (`OpsOk`), room for its changes, the leases its puts name known (`checkTxn`'s) and
those of the state (not for the read-only wrapper). At a context that may be done (`nd = false`,
only for the read-only wrapper; 2026-10-12, the request path's unit 3b), a range may fail with
the context error: `executeTxn` returns `fmt.Errorf`'s wrapping of it (`mvcc.errorfIs`). -/
abbrev txn.executeTxn.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg s : Loc)
    (γ : mvcc.StoreNames) (tw : GoInterface) (ro : Bool) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (rt : Loc) (t : TxnModel) (pl : GoSlice) (rest : List Bool) (tresp : Loc) (skip : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ txn.txnWriteIs tw s γ ro ilog pend ∗ mvcc.txnCtx ctx cd ∗
      (if nd then mvcc.neverDone cd else iprop(True)) ∗
      txn.txnRequestIs rt t ∗ pl ↦*□ (txn.txnPath (mvcc.stateAfter ilog) t ++ rest) ∗
      txn.respsSkel (mvcc.stateAfter ilog) tresp (t.branch (txn.txnOk (mvcc.stateAfter ilog) t)) ∗
      txn.leasesOk γ.leases (txn.opsLeases (mvcc.stateAfter ilog)
        (t.branch (txn.txnOk (mvcc.stateAfter ilog) t))) ∗
      (if ro then iprop(True) else txn.leasesKnown γ.leases (txn.pendState ilog pend)) ∗
      ⌜txn.OpsOk false (mvcc.stateAfter ilog) (W64 (ilog.length : Int)) (txn.pendState ilog pend)
          (t.branch (txn.txnOk (mvcc.stateAfter ilog) t)) ∧
        pend.length + (txn.srvOps (mvcc.stateAfter ilog) (W64 (ilog.length : Int))
          (txn.pendState ilog pend) (t.branch (txn.txnOk (mvcc.stateAfter ilog) t))).1.length <
          2 ^ 63 ∧
        (ro = true → ∀ op ∈ t.branch (txn.txnOk (mvcc.stateAfter ilog) t), txn.opIsGet op = true) ∧
        (nd = false → ro = true)⌝ }}
    (App (App (App (App (App (App (App (Val (@! txn.executeTxn)) (Val #(GoInterface.ok ctx)))
      (Val #lg)) (Val #tw)) (Val #rt)) (Val #pl)) (Val #tresp)) (Val #skip))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      (⌜err = GoInterface.nil ∧ n = W64 (txn.nestedCount (mvcc.stateAfter ilog) t : Int)⌝ ∗
        txn.txnWriteIs tw s γ ro ilog (pend ++ (txn.srvOps (mvcc.stateAfter ilog)
          (W64 (ilog.length : Int)) (txn.pendState ilog pend)
          (t.branch (txn.txnOk (mvcc.stateAfter ilog) t))).1) ∗
        txn.respsIs skip tresp (t.branch (txn.txnOk (mvcc.stateAfter ilog) t))
          (txn.srvOps (mvcc.stateAfter ilog) (W64 (ilog.length : Int)) (txn.pendState ilog pend)
            (t.branch (txn.txnOk (mvcc.stateAfter ilog) t))).2 ∗
        (if ro then iprop(True) else
          txn.leasesKnown γ.leases (txn.pendState ilog (pend ++ (txn.srvOps (mvcc.stateAfter ilog)
            (W64 (ilog.length : Int)) (txn.pendState ilog pend)
            (t.branch (txn.txnOk (mvcc.stateAfter ilog) t))).1)))) ∨
      (⌜nd = false⌝ ∗ mvcc.errorfIs err ∗
        ∃ pend' : List mvcc.Change, txn.txnWriteIs tw s γ ro ilog pend') }}

end spec

end EtcdGrove
end Perennial
