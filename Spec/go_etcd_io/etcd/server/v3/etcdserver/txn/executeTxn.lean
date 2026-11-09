/-
`executeTxn(ctx, lg, txnWrite, rt, txnPath, tresp, skip)` (`txn.go`), internal (`txn`, recursively).
**Proof sketch.** Per operation of the taken branch: `executeRange` (no view error: the checks
passed at `σ.kv`, and the view's revision is `σ.rev` or one more; `skip`: the header only),
`getPrevKV` and `put` (an ignore key present: the premise, kept by `opsSafe` across the branch's
deletes; the lease live: `opsCheck`, `leasesLive`), `deleteRange`, a nested `executeTxn` (its
path the rest). Old spec: over the log, `PathsIgnOk`. Round 1: 3e's API (F4); the lessor's state
after by `evsLs` of the new events.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

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

/-- `executeTxn(ctx, lg, tw, rt, path, tresp, skip)` on an open transaction begun at `σ` with the events
`pend` (a read one: none): `execOps` of the taken branch from the current store, filling the response
tree (header revision `0`); or the context's error. -/
def executeTxn.spec : Prop :=
  ∀ (ctx : GoInterface) (lg : Loc) (tw : GoInterface) (γ : Mvcc.MvccName) (tr : Loc) (w : Bool)
    (σ : Mvcc.MvccState) (pend : List Event) (rt : Loc) (dq : DFrac) (t : TxnReq) (path : GoSlice)
    (rest : List Bool) (tresp : Loc) (skip : Bool) (γl : Lease.Names) (n : Nat)
    (ls : Lease.LessorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ Zap.isLogger lg ∗ TraceUtil.ctxTraceIs ctx (some tr) ∗
      TraceUtil.traceOwn tr ∗ Mvcc.mvccTxn tw γ tr (txnK w σ pend) ∗ txnReqOwn rt dq t ∗
      path ↦*□ (txnPathOf t σ.kv.store ++ rest) ∗
      respSkel tresp σ.kv.store (cmpsHold t.compare σ.kv.store) (if cmpsHold t.compare σ.kv.store then t.success else t.failure) ∗
      ⌜opsSafe (if cmpsHold t.compare σ.kv.store then t.success else t.failure) ∧ opsCheck σ.kv ls.table (if cmpsHold t.compare σ.kv.store then t.success else t.failure) = none ∧
        (∀ key ∈ opsIgnTaken σ.kv.store (if cmpsHold t.compare σ.kv.store then t.success else t.failure), Mvcc.txnStore σ pend key ≠ none) ∧
        (w = true ∨ (pend = [] ∧ ∀ op ∈ (if cmpsHold t.compare σ.kv.store then t.success else t.failure), ∃ r, op = .range r))⌝ ∗
      (if w then iprop(Mvcc.mvccLessorIs γ γl ∗ Lease.lessorState γl n ls ∗
         ⌜leasesLive (Mvcc.txnStore σ pend) ls⌝)
       else iprop(True)) }}
    (App (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.executeTxn)) (Val #ctx)) (Val #lg)) (Val #tw)) (Val #rt)) (Val #path)) (Val #tresp)) (Val #skip))
  {{ (cnt : w64) (err : GoInterface), RET (PairV #cnt #err); TraceUtil.traceOwn tr ∗
      txnReqOwn rt dq t ∗
      ((⌜err = GoInterface.nil ∧ cnt = W64 ((txnPathOf t σ.kv.store).length - 1)⌝ ∗
          Mvcc.mvccTxn tw γ tr (txnK w σ (execOps σ.kv skip (Mvcc.txnStore σ pend, pend) (if cmpsHold t.compare σ.kv.store then t.success else t.failure)).1.2) ∗
          (if w then iprop(∃ n' : Nat, Lease.lessorState γl n'
              (evsLs ls (Mvcc.txnStore σ pend) ((execOps σ.kv skip (Mvcc.txnStore σ pend, pend) (if cmpsHold t.compare σ.kv.store then t.success else t.failure)).1.2.drop pend.length)))
           else iprop(True)) ∗
          ∃ m : TxnRespM, txnRespOwn tresp (DFrac.own 1) m ∗
            ⌜m.hdr = hdrAt 0 ∧ m.ofResps (cmpsHold t.compare σ.kv.store) (execOps σ.kv skip (Mvcc.txnStore σ pend, pend) (if cmpsHold t.compare σ.kv.store then t.success else t.failure)).2⌝) ∨
       (∃ pend' : List Event, Mvcc.mvccTxn tw γ tr (txnK w σ pend') ∗ Context.ctxDone ctx ∗ ctxErr err ∗
          (if w then iprop(∃ (n' : Nat) (ls' : Lease.LessorState), Lease.lessorState γl n' ls')
           else iprop(True)))) }}

end spec
end Txn
end EtcdGrove
end Perennial
