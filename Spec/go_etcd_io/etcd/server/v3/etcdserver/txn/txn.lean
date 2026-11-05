/-
`txn` (`txn.go`). Lean-first; see `TxnRun.lean`, `InvTxn.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiVocab
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvWarn

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccReachable MvccName MvccStorage mvccN mvccLeases)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn

set_option linter.iris.dupNamespace false in
/-- `txn(ctx, lg, txnWrite, rt, isWrite, txnPath, skip)` on a fresh write transaction begun at `σ`
(`isWrite`), or the read-only wrapper of a read transaction at `σ`.

(Strict M1, 2026-11-05: restated over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean`
drafts it, frozen; `notes/mvcc-api-clients/clients-txn.md`. The pending premise only for a write
transaction, `ro = false → σ.pending = none`, decided by the coordinator, 2026-11-05: a read
transaction's state may have a pending revision.) -/
abbrev txn.txn.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg : Loc)
    (γ : MvccName) (trace : Loc) (te : Bool) (tw : GoInterface) (ro : Bool) (σ : MvccState)
    (rt : Loc) (t : TxnModel) (pl : GoSlice) (skip : Bool) (L : List w64),
  let k : MTxn := if ro then .read σ else .write σ []
  let chs := txn.txnChs σ.log t
  {{ pkgInit ∗ mvcc.api.mvccTxn tw γ trace k ∗ traceutil.ownTrace trace te ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx (some trace) ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
      txn.txnRequestIs rt t ∗ pl ↦*□ txn.txnPath (mvcc.stateAfter σ.log) t ∗
      txn.leasesOk L (txn.opsLeases (mvcc.stateAfter σ.log)
        (t.branch (txn.txnOk (mvcc.stateAfter σ.log) t))) ∗
      (if ro then iprop(True) else txn.leasesKnown L (mvcc.stateAfter σ.log)) ∗
      (⌜ro = true⌝ ∨ lease.leaseOwn (mvccLeases γ) L (mvcc.leaseItemsOf (mvcc.stateAfter σ.log))) ∗
      ⌜txn.Reach σ ∧ (ro = false → σ.pending = none) ∧
        txn.OpsOk false (mvcc.stateAfter σ.log) (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log)
          (t.branch (txn.txnOk (mvcc.stateAfter σ.log) t)) ∧
        (ro = true → txn.txnReadonly t = true) ∧ (nd = false → ro = true ∧ lg ≠ null)⌝ }}
    (App (App (App (App (App (App (App (Val (@! txn.txn)) (Val #(GoInterface.ok ctx))) (Val #lg))
      (Val #tw)) (Val #rt)) (Val #(!ro))) (Val #pl)) (Val #skip))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); traceutil.ownTrace trace te ∗
      ((⌜err = GoInterface.nil ∧ (ro = true → chs = [])⌝ ∗
        mvcc.api.mvccTxn tw γ trace (txn.MTxn.append k chs) ∗
        txn.txnResponseIs skip resp (W64 (mvcc.writeRev σ.log chs : Int)) t
          (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).1
          (txn.srvRunTxn (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) t).2.2 ∗
        txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp) ∗
        (if ro then iprop(True) else
          txn.leasesKnown L (mvcc.applyChanges (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) chs)) ∗
        (⌜ro = true⌝ ∨ lease.leaseOwn (mvccLeases γ) L (mvcc.leaseItemsOf (mvcc.applyChanges
          (W64 (σ.log.length : Int)) (mvcc.stateAfter σ.log) chs)))) ∨
      (⌜nd = false⌝ ∗ mvcc.errorfIs err ∗ mvcc.api.mvccTxn tw γ trace k ∗
        txn.txnRespShell resp ∗ txn.roTxnRespRd resp ∗
        txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" resp))) }}

end spec

end EtcdGrove
end Perennial
