/-
`txn(ctx, lg, txnWrite, rt, isWrite, txnPath, skip)` (`txn.go`), internal (`Txn`). **Proof sketch.**
`newTxnResp`, `executeTxn` (from the begin state, no events), an error: `lg.Panic` for a write
(excluded: the context never done, so `executeTxn` returns none), `lg.Error` for a read-only one;
the header's revision from the transaction's `Rev()` and `Changes()` (3e: `h.rev`, the pending
events). Old spec: over the log.
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

open Classical in
/-- `txn(ctx, lg, tw, rt, isWrite, path, skip)` on an open transaction begun at `h` (kind `.write`
or the read-only wrapper), the checks passed: the responses of `execOps` on the taken branch, the
header's revision `runRev`; or a read-only transaction's context error. -/
def txn.spec : Prop :=
  ∀ (ctx : GoInterface) (lg : Loc) (tw : GoInterface) (γ : MvccName) (h : KVHist) (rt : Loc)
    (dq : DFrac) (t : TxnReq) (isWrite : Bool) (path : GoSlice) (skip : Bool)
    (ls : Int → Option LeaseRec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ Zap.isLogger lg ∗
      mvccTxn tw γ (if isWrite then .write else .roWrite) h [] ∗ txnReqOwn rt dq t ∗
      path ↦*□ txnPathOf t h.store ∗
      ⌜txnSafe t ∧ opsCheck h ls (if cmpsHold t.compare h.store then t.success else t.failure) = none ∧ isWrite = !decide t.readonly⌝ ∗
      (if isWrite then iprop(leasesPin γ ls ∗ ⌜leasesLive h.store ls⌝ ∗ (Context.ctxDone ctx -∗ False))
       else iprop(True)) }}
    (App (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.txn)) (Val #ctx)) (Val #lg)) (Val #tw)) (Val #rt)) (Val #isWrite)) (Val #path)) (Val #skip))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); txnReqOwn rt dq t ∗
      (if isWrite then leasesPin γ ls else iprop(True)) ∗
      mvccTxn tw γ (if isWrite then .write else .roWrite) h
        (execOps h skip (h.store, []) (if cmpsHold t.compare h.store then t.success else t.failure)).1.2 ∗
      ((⌜err = GoInterface.nil⌝ ∗
          txnOk resp (runRev h (execOps h skip (h.store, []) (if cmpsHold t.compare h.store then t.success else t.failure)).1.2) (cmpsHold t.compare h.store)
            (execOps h skip (h.store, []) (if cmpsHold t.compare h.store then t.success else t.failure)).2) ∨
       (⌜isWrite = false⌝ ∗ Context.ctxDone ctx ∗ ctxErr err ∗ roTxnResp resp)) }}

end spec
end Txn
end EtcdGrove
end Perennial
