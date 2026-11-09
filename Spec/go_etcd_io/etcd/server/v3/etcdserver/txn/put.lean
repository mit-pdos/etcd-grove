/-
`put(ctx, txnWrite, p, prevKV)` (`put.go`), internal (`Put`, `executeTxn`). **Proof sketch.**
`traceutil.Get(ctx)` (4b); the value and lease from `prevKV.KVs[0]` for an ignore flag (present: the
premise; else the index panics, `issues/etcd-txn-delete-then-ignore-put.md`); the transaction's `Put`
(3e: the pending event, the revision `h.rev + 1`; the store's lessor `GetLease`, `Detach`es the old
lease and `Attach`es the new one at the writer's token, live: the premise, else mvcc panics; keeping
`attached`). Old spec: over the log, `leaseOk`.
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

/-- `put(ctx, tw, p, prevKV)` in an open write transaction (begun at `h`, pending `evs`), `prevKV`
the key's record `cur` in the pending store if the request needs it (`nil` otherwise): the put's
event over `cur`, the reply at revision `h.rev + 1`. -/
def put.spec : Prop :=
  ∀ (ctx tw : GoInterface) (γ : MvccName) (h : KVHist) (evs : List Event) (p : Loc) (dq : DFrac)
    (pm : PutReq) (prevKV : Loc) (leL : Loc) (γl : Lease.Names) (c : Lease.Cfg) (n : Nat)
    (ls : Lease.LessorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ mvccTxn tw γ .write h evs ∗ Lease.isLessor leL γl c ∗
      mvccLessor γ γl ∗ Lease.lessorState γl n ls ∗ ⌜attached (h.store.applyEvents evs) ls⌝ ∗
      putReqOwn p dq pm ∗
      (if needsPrev pm then
         rrOwn prevKV (((h.store.applyEvents evs) pm.key).map (KV.ofRec pm.key)).toList
           (viewRev h evs) ((h.store.applyEvents evs) pm.key).toList.length
       else iprop(⌜prevKV = null⌝)) ∗
      ⌜(ignores pm = true → (h.store.applyEvents evs) pm.key ≠ none) ∧
        ((pm.record (h.rev + 1) ((h.store.applyEvents evs) pm.key)).lease = 0 ∨
          ls.leases (pm.record (h.rev + 1) ((h.store.applyEvents evs) pm.key)).lease ≠ none)⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.put)) (Val #ctx)) (Val #tw)) (Val #p)) (Val #prevKV))
  {{ (resp : Loc), RET #resp; putReqOwn p dq pm ∗
      (∃ (n' : Nat) (ls' : Lease.LessorState), Lease.lessorState γl n' ls' ∗
        ⌜sameLeases ls ls' ∧ attached ((h.store.applyEvents evs).applyEvent
          (.put pm.key (pm.record (h.rev + 1) ((h.store.applyEvents evs) pm.key)))) ls'⌝) ∗
      mvccTxn tw γ .write h
        (evs ++ [.put pm.key (pm.record (h.rev + 1) ((h.store.applyEvents evs) pm.key))]) ∗
      putOk resp (h.rev + 1)
        (if pm.prevKv then ((h.store.applyEvents evs) pm.key).map (KV.ofRec pm.key) else none) }}

end spec
end Txn
end EtcdGrove
end Perennial
