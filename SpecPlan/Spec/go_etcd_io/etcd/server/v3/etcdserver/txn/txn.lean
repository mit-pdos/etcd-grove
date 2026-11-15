/-
`txn(ctx, lg, txnWrite, rt, isWrite, txnPath, skip)` (`txn.go`), internal (`Txn`). **Proof sketch.**
`newTxnResp`, `executeTxn` (from the begin state, no events), an error: `lg.Panic` for a write
(excluded: the context never done, so `executeTxn` returns none), `lg.Error` for a read-only one;
the header's revision from the transaction's `Rev()` and `Changes()` (3e: `σ.rev`, the events).
Old spec: over the log. Round 1: 3e's API (F4).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

open Classical in
/-- `txn(ctx, lg, tw, rt, isWrite, path, skip)` on an open transaction begun at `σ` (a write one, or
the read-only wrapper), the checks passed: the responses of `execOps` on the taken branch, the
header's revision `runRev`; or a read-only transaction's context error. -/
def txn.spec : Prop :=
  ∀ (ctx : GoInterface) (lg : Loc) (tw : GoInterface) (γ : Mvcc.MvccName) (tr : Loc)
    (σ : Mvcc.MvccState) (rt : Loc) (dq : DFrac) (t : TxnReq) (isWrite : Bool) (path : GoSlice)
    (skip : Bool) (γl : Lease.Names) (n : Nat) (ls : Lease.LessorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ Zap.isLogger lg ∗ TraceUtil.ctxTraceIs ctx (some tr) ∗
      TraceUtil.traceOwn tr ∗ Mvcc.mvccTxn tw γ tr (txnK isWrite σ []) ∗ txnReqOwn rt dq t ∗
      path ↦*□ txnPathOf t σ.kv.store ∗
      ⌜txnSafe t ∧ opsCheck σ.kv ls.table (if cmpsHold t.compare σ.kv.store then t.success else t.failure) = none ∧ isWrite = !decide t.readonly⌝ ∗
      (if isWrite then iprop(Mvcc.mvccLessorIs γ γl ∗ Lease.lessorState γl n ls ∗
         ⌜leasesLive σ.kv.store ls⌝ ∗ (Context.ctxDone ctx -∗ False))
       else iprop(True)) }}
    (App (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.txn)) (Val #ctx)) (Val #lg)) (Val #tw)) (Val #rt)) (Val #isWrite)) (Val #path)) (Val #skip))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); TraceUtil.traceOwn tr ∗
      txnReqOwn rt dq t ∗ Mvcc.mvccTxn tw γ tr (txnK isWrite σ (execOps σ.kv skip (σ.kv.store, []) (if cmpsHold t.compare σ.kv.store then t.success else t.failure)).1.2) ∗
      (if isWrite then iprop(∃ n' : Nat, Lease.lessorState γl n' (evsLs ls σ.kv.store (execOps σ.kv skip (σ.kv.store, []) (if cmpsHold t.compare σ.kv.store then t.success else t.failure)).1.2))
       else iprop(True)) ∗
      ((⌜err = GoInterface.nil⌝ ∗
          txnOk resp (runRev σ.kv (execOps σ.kv skip (σ.kv.store, []) (if cmpsHold t.compare σ.kv.store then t.success else t.failure)).1.2) (cmpsHold t.compare σ.kv.store) (execOps σ.kv skip (σ.kv.store, []) (if cmpsHold t.compare σ.kv.store then t.success else t.failure)).2) ∨
       (⌜isWrite = false⌝ ∗ Context.ctxDone ctx ∗ ctxErr err ∗ roTxnResp resp)) }}

end spec
end Txn
end EtcdGrove
end Perennial
