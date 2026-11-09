/-
`executeTxn(ctx, lg, txnWrite, rt, txnPath, tresp, skip)` (`txn.go`), internal (`txn`, recursively).
**Proof sketch.** Per operation of the taken branch: `executeRange` (no view error: the checks
passed at `h`, and the view's revision is `h.rev` or one more; `skip`: the header only),
`getPrevKV` and `put` (an ignore key present: the premise, kept by `opsSafe` across the branch's
deletes; the lease live: `opsCheck`, `attached`), `deleteRange`, a nested `executeTxn` (its
path the rest). Old spec: over the log, `PathsIgnOk`.
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

/-- `executeTxn(ctx, lg, tw, rt, path, tresp, skip)` on an open transaction (begun at `h`, pending
`evs`): `execOps` of the taken branch from the pending store, filling the response tree (header
revision `0`); or the context's error. -/
def executeTxn.spec : Prop :=
  ∀ (ctx : GoInterface) (lg : Loc) (tw : GoInterface) (γ : MvccName) (k : TxKind) (h : KVHist)
    (evs : List Event) (rt : Loc) (dq : DFrac) (t : TxnReq) (path : GoSlice) (rest : List Bool)
    (tresp : Loc) (skip : Bool) (leL : Loc) (γl : Lease.Names) (c : Lease.Cfg) (n : Nat)
    (ls : Lease.LessorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ Zap.isLogger lg ∗ mvccTxn tw γ k h evs ∗ txnReqOwn rt dq t ∗
      path ↦*□ (txnPathOf t h.store ++ rest) ∗
      respSkel tresp h.store (cmpsHold t.compare h.store) (if cmpsHold t.compare h.store then t.success else t.failure) ∗
      ⌜opsSafe (if cmpsHold t.compare h.store then t.success else t.failure) ∧ opsCheck h ls.table (if cmpsHold t.compare h.store then t.success else t.failure) = none ∧
        (∀ key ∈ opsIgnTaken h.store (if cmpsHold t.compare h.store then t.success else t.failure), (h.store.applyEvents evs) key ≠ none) ∧
        (k = .write ∨ ∀ op ∈ (if cmpsHold t.compare h.store then t.success else t.failure), ∃ r, op = .range r)⌝ ∗
      (match k with
       | .write => iprop(Lease.isLessor leL γl c ∗ mvccLessor γ γl ∗ Lease.lessorState γl n ls ∗
           ⌜attached (h.store.applyEvents evs) ls⌝)
       | _ => iprop(True)) }}
    (App (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.executeTxn)) (Val #ctx)) (Val #lg)) (Val #tw)) (Val #rt)) (Val #path)) (Val #tresp)) (Val #skip))
  {{ (cnt : w64) (err : GoInterface), RET (PairV #cnt #err); txnReqOwn rt dq t ∗
      ((⌜err = GoInterface.nil ∧ cnt = W64 ((txnPathOf t h.store).length - 1)⌝ ∗
          mvccTxn tw γ k h (execOps h skip (h.store.applyEvents evs, evs) (if cmpsHold t.compare h.store then t.success else t.failure)).1.2 ∗
          (match k with
           | .write => iprop(∃ (n' : Nat) (ls' : Lease.LessorState), Lease.lessorState γl n' ls' ∗
               ⌜sameLeases ls ls' ∧ attached (h.store.applyEvents (execOps h skip (h.store.applyEvents evs, evs) (if cmpsHold t.compare h.store then t.success else t.failure)).1.2) ls'⌝)
           | _ => iprop(True)) ∗
          ∃ m : TxnRespM, txnRespOwn tresp (DFrac.own 1) m ∗
            ⌜m.hdr = hdrAt 0 ∧ m.ofResps (cmpsHold t.compare h.store) (execOps h skip (h.store.applyEvents evs, evs) (if cmpsHold t.compare h.store then t.success else t.failure)).2⌝) ∨
       (∃ evs' : List Event, mvccTxn tw γ k h evs' ∗ Context.ctxDone ctx ∗ ctxErr err ∗
          (match k with
           | .write => iprop(∃ (n' : Nat) (ls' : Lease.LessorState), Lease.lessorState γl n' ls')
           | _ => iprop(True)))) }}

end spec
end Txn
end EtcdGrove
end Perennial
