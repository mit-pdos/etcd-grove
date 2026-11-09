/-
`executeRange(ctx, lg, txnRead, r, withTotalCount)` (`range.go`), internal (`Range`, `executeTxn`).

**Proof sketch.** `traceutil.Get(ctx)` (4b), `rangeLimit`, `mkGteRange` (an empty `RangeEnd` is `nil`,
W0's request law: the key alone), mvcc's transaction `Range` (3e, at the open transaction: the view's
error, else an `rrOwn` result of the range's keys at `viewStore`, its length at most `2 ^ 62`, the
limit and keys-only fetch of `rangeOut`, the count; or the context's error),
`filterRangeResults`, `sortRangeResults`, `asembleRangeResponse`. Old spec: over the log.
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

/-- `executeRange(ctx, lg, tx, r, wtc)` on an open transaction (begun at `h`, pending `evs`): the
view's revision error, or the reply `rangeOut` at the view's revision, or the context's error. -/
def executeRange.spec : Prop :=
  ∀ (ctx : GoInterface) (lg : Loc) (tx : GoInterface) (γ : MvccName) (k : TxKind) (h : KVHist)
    (evs : List Event) (r : Loc) (dq : DFrac) (rm : RangeReq) (wtc : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ Zap.isLogger lg ∗ mvccTxn tx γ k h evs ∗ rangeReqOwn r dq rm ∗
      ⌜targetOk rm⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.executeRange)) (Val #ctx)) (Val #lg)) (Val #tx)) (Val #r)) (Val #wtc))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); mvccTxn tx γ k h evs ∗ rangeReqOwn r dq rm ∗
      ((∃ e : EtcdErr, ⌜viewErr h evs rm.revision = some e ∧ resp = null⌝ ∗ errIs err e) ∨
       (⌜viewErr h evs rm.revision = none ∧ err = GoInterface.nil⌝ ∗ ∃ all : List KV,
          ⌜(viewStore h evs rm.revision).rangeKVs rm.range all⌝ ∗
          rangeOk resp (viewRev h evs) (rangeOut rm wtc all)) ∨
       (⌜resp = null⌝ ∗ Context.ctxDone ctx ∗ ctxErr err)) }}

end spec
end Txn
end EtcdGrove
end Perennial
