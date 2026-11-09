/-
`deleteRange(ctx, txnWrite, dr)` (`delete.go`), internal (`DeleteRange`, `executeTxn`).
**Proof sketch.** `mkGteRange`; with `PrevKv`, the transaction's `Range` at revision `0` (3e's
`Txn.Range`: the pending store's keys, or the context's error); the transaction's `DeleteRange` (3e:
the present keys of the pending store deleted, `delsLs` on the lessor's token, `(n, rev)` with `rev`
the view's revision after). Old spec: over the log. Round 1: 3e's API (F4).
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

/-- `deleteRange(ctx, tw, dr)` in an open write transaction (begun at `σ`, pending `pend`): the range's
present keys `l` of the pending store deleted, the reply at the view's revision after; or, with
`PrevKv`, the context's error, nothing deleted. -/
def deleteRange.spec : Prop :=
  ∀ (ctx tw : GoInterface) (γ : Mvcc.MvccName) (tr : Loc) (σ : Mvcc.MvccState) (pend : List Event)
    (γl : Lease.Names) (n : Nat) (ls : Lease.LessorState) (d : Loc) (dq : DFrac) (dm : DeleteReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ TraceUtil.traceOwn tr ∗ Mvcc.mvccTxn tw γ tr (.write σ pend) ∗
      Mvcc.mvccLessorIs γ γl ∗ Lease.lessorState γl n ls ∗ deleteReqOwn d dq dm }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.deleteRange)) (Val #ctx)) (Val #tw)) (Val #d))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); TraceUtil.traceOwn tr ∗
      deleteReqOwn d dq dm ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ l : List KV, ⌜(Mvcc.txnStore σ pend).rangeKVs dm.range l⌝ ∗
          Mvcc.mvccTxn tw γ tr (.write σ (pend ++ delEvents l)) ∗
          (∃ n' : Nat, Lease.lessorState γl n' (Mvcc.delsLs ls (l.map (·.key)))) ∗
          delOk resp (viewRev (.write σ (pend ++ delEvents l))) l.length (if dm.prevKv then l else [])) ∨
       (⌜resp = null ∧ dm.prevKv = true⌝ ∗ Mvcc.mvccTxn tw γ tr (.write σ pend) ∗
          Lease.lessorState γl n ls ∗ Context.ctxDone ctx ∗ ctxErr err)) }}

end spec
end Txn
end EtcdGrove
end Perennial
