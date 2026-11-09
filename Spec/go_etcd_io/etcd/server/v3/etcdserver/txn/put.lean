/-
`put(ctx, txnWrite, p, prevKV)` (`put.go`), internal (`Put`, `executeTxn`). **Proof sketch.**
`traceutil.Get(ctx)` (4b); the value and lease from `prevKV.KVs[0]` for an ignore flag (present: the
premise; else the index panics, `issues/etcd-txn-delete-then-ignore-put.md`); the transaction's `Put`
(3e's `Txn.Put.contract`: `putEv` with that value and lease, which is `pm.record`'s event; the
lessor's token by `putLs`; the lease live: the premise, else mvcc panics). Old spec: over the log.
Round 1: 3e's API (F4).
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

/-- `put(ctx, tw, p, prevKV)` in an open write transaction (begun at `σ`, pending `pend`), `prevKV` the
key's record in the pending store if the request needs it (`nil` otherwise): the put's event over
it, the reply at revision `σ.rev + 1`. -/
def put.spec : Prop :=
  ∀ (ctx tw : GoInterface) (γ : Mvcc.MvccName) (tr : Loc) (σ : Mvcc.MvccState) (pend : List Event)
    (p : Loc) (dq : DFrac) (pm : PutReq) (prevKV : Loc) (γl : Lease.Names) (n : Nat)
    (ls : Lease.LessorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ TraceUtil.ctxTraceIs ctx (some tr) ∗ TraceUtil.traceOwn tr ∗
      Mvcc.mvccTxn tw γ tr (.write σ pend) ∗ Mvcc.mvccLessorIs γ γl ∗ Lease.lessorState γl n ls ∗
      putReqOwn p dq pm ∗
      (if needsPrev pm then
         rrOwn prevKV ((Mvcc.txnStore σ pend pm.key).map (KV.ofRec pm.key)).toList (viewRev (.write σ pend)) (Mvcc.txnStore σ pend pm.key).toList.length
       else iprop(⌜prevKV = null⌝)) ∗
      ⌜(ignores pm = true → (Mvcc.txnStore σ pend pm.key) ≠ none) ∧ ((pm.record (σ.rev + 1) (Mvcc.txnStore σ pend pm.key)).lease = 0 ∨ ls.leases (pm.record (σ.rev + 1) (Mvcc.txnStore σ pend pm.key)).lease ≠ none)⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.put)) (Val #ctx)) (Val #tw)) (Val #p)) (Val #prevKV))
  {{ (resp : Loc), RET #resp; TraceUtil.traceOwn tr ∗ putReqOwn p dq pm ∗
      Mvcc.mvccTxn tw γ tr (.write σ (pend ++ [.put pm.key (pm.record (σ.rev + 1) (Mvcc.txnStore σ pend pm.key))])) ∗
      (∃ n' : Nat, Lease.lessorState γl n' (Mvcc.putLs ls (Mvcc.txnStore σ pend pm.key).isSome pm.key (pm.record (σ.rev + 1) (Mvcc.txnStore σ pend pm.key)).lease)) ∗
      putOk resp (σ.rev + 1) (if pm.prevKv then (Mvcc.txnStore σ pend pm.key).map (KV.ofRec pm.key) else none) }}

end spec
end Txn
end EtcdGrove
end Perennial
