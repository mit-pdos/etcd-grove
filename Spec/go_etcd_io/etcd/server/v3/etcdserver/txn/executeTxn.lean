/-
`executeTxn` (`txn.go`). Lean-first; see `TxnRun.lean`, `InvTxn.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiVocab
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvWarn
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs

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

/-- `executeTxn(ctx, lg, txnWrite, rt, txnPath, tresp, skip)` at a transaction `k`: a write one
(begun at `σ`, `pend` pending), or (`k.isRead`) the read-only wrapper of a read transaction at
`σ`. No size premise (each get's sort from its range's `stateOk`).

(Strict M1, 2026-11-05: restated over mvcc's API as `notes/mvcc-api-clients/TxnSpecs.lean`
drafts it, frozen; `notes/mvcc-api-clients/clients-txn.md`.) -/
abbrev txn.executeTxn.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (nd : Bool) (lg : Loc)
    (γ : MvccName) (trace : Loc) (te : Bool) (tw : GoInterface) (k : MTxn) (rt : Loc)
    (t : TxnModel) (pl : GoSlice) (rest : List Bool) (tresp : Loc) (skip : Bool) (L : List w64),
  let s0 := mvcc.stateAfter k.state.log
  let ops := t.branch (txn.txnOk s0 t)
  let run := txn.srvOps s0 (W64 (k.state.log.length : Int)) (txn.mstate k) ops
  {{ pkgInit ∗ mvcc.api.mvccTxn tw γ trace k ∗ traceutil.ownTrace trace te ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx (some trace) ∗ (if nd then mvcc.neverDone cd else iprop(True)) ∗
      txn.txnRequestIs rt t ∗ pl ↦*□ (txn.txnPath s0 t ++ rest) ∗ txn.respsSkel s0 tresp ops ∗
      txn.leasesOk L (txn.opsLeases s0 ops) ∗
      (if txn.MTxn.isRead k then iprop(True) else txn.leasesKnown L (txn.mstate k)) ∗
      (⌜txn.MTxn.isRead k = true⌝ ∨ lease.leaseOwn (mvccLeases γ) L (mvcc.pendItems k.state.log k.pend)) ∗
      ⌜txn.Reach k.state ∧
        txn.OpsOk false s0 (W64 (k.state.log.length : Int)) (txn.mstate k) ops ∧
        (txn.MTxn.isRead k = true → ∀ op ∈ ops, txn.opIsGet op = true) ∧
        (nd = false → txn.MTxn.isRead k = true)⌝ }}
    (App (App (App (App (App (App (App (Val (@! txn.executeTxn)) (Val #(GoInterface.ok ctx)))
      (Val #lg)) (Val #tw)) (Val #rt)) (Val #pl)) (Val #tresp)) (Val #skip))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err); traceutil.ownTrace trace te ∗
      ((⌜err = GoInterface.nil ∧ n = W64 (txn.nestedCount s0 t : Int) ∧
            (txn.MTxn.isRead k = true → run.1 = [])⌝ ∗
        mvcc.api.mvccTxn tw γ trace (txn.MTxn.append k run.1) ∗
        txn.respsIs skip tresp ops run.2 ∗
        (if txn.MTxn.isRead k then iprop(True)
         else txn.leasesKnown L (txn.mstate (txn.MTxn.append k run.1))) ∗
        (⌜txn.MTxn.isRead k = true⌝ ∨ lease.leaseOwn (mvccLeases γ) L
          (mvcc.pendItems k.state.log (k.pend ++ run.1)))) ∨
      (⌜nd = false⌝ ∗ mvcc.errorfIs err ∗ mvcc.api.mvccTxn tw γ trace k ∗ txn.roRespsRd tresp)) }}

end spec

end EtcdGrove
end Perennial
