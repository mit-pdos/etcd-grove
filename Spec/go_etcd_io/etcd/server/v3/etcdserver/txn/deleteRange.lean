/-
`deleteRange(ctx, txnWrite, dr)` (`delete.go`), internal (`DeleteRange`, `executeTxn`).
**Proof sketch.** `mkGteRange`; with `PrevKv`, the transaction's `Range` at revision `0` (3e: the
pending store's keys, or the context's error); the transaction's `DeleteRange` (3e: the range's
present keys of the pending store deleted, `(n, rev)` with `rev` the view's revision after; each
key's lease detached through the store's lessor, `GetLease`/`Detach` at the writer's token, keeping
`attached`). Old spec: over the log.
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

/-- `deleteRange(ctx, tw, dr)` in an open write transaction (begun at `h`, pending `evs`): the
range's present keys `l` of the pending store deleted, the reply at the view's revision after; or,
with `PrevKv`, the context's error, nothing deleted. -/
def deleteRange.spec : Prop :=
  ∀ (ctx tw : GoInterface) (γ : MvccName) (h : KVHist) (evs : List Event) (leL : Loc)
    (γl : Lease.Names) (c : Lease.Cfg) (n : Nat) (ls : Lease.LessorState) (d : Loc) (dq : DFrac)
    (dm : DeleteReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ mvccTxn tw γ .write h evs ∗ Lease.isLessor leL γl c ∗
      mvccLessor γ γl ∗ Lease.lessorState γl n ls ∗ ⌜attached (h.store.applyEvents evs) ls⌝ ∗
      deleteReqOwn d dq dm }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.deleteRange)) (Val #ctx)) (Val #tw)) (Val #d))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); deleteReqOwn d dq dm ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ l : List KV, ⌜(h.store.applyEvents evs).rangeKVs dm.range l⌝ ∗
          mvccTxn tw γ .write h (evs ++ delEvents l) ∗
          (∃ (n' : Nat) (ls' : Lease.LessorState), Lease.lessorState γl n' ls' ∗
            ⌜sameLeases ls ls' ∧ attached (h.store.applyEvents (evs ++ delEvents l)) ls'⌝) ∗
          delOk resp (viewRev h (evs ++ delEvents l)) l.length (if dm.prevKv then l else [])) ∨
       (⌜resp = null ∧ dm.prevKv = true⌝ ∗ mvccTxn tw γ .write h evs ∗ Lease.lessorState γl n ls ∗
          Context.ctxDone ctx ∗ ctxErr err)) }}

end spec
end Txn
end EtcdGrove
end Perennial
