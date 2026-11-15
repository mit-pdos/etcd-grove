/-
`executeRange(ctx, lg, txnRead, r, withTotalCount)` (`range.go`), internal (`Range`, `executeTxn`).

**Proof sketch.** `traceutil.Get(ctx)` (4b: the context's trace `tr`, owned), `rangeLimit`,
`mkGteRange` (the end as W0 reads it: F1's mapping), the transaction's `Range` (3e's
`Txn.Range.contract`: `rangeOut k.readHist k.state.crev`; the result `rangeResOwn`, whose `.ok`
case is `rrOwn` of the cut key-values, `keysOnlyM` on the fast path, i.e. `ofKV` of the key-value
with no value and lease `0`, `kvsFit`), `filterRangeResults`, `sortRangeResults` (its size premise
from `kvsFit`), `asembleRangeResponse`. Old spec: over the log. Round 1: 3e's API (F4); the
keys-only path's values (F2). Integration (I5, 2026-11-09): the context's error only for a full
read (`rm.countOnly = false`: mvcc's `rangeOut`'s `.ctxErr` case asks `CountOnly = false`), which
`Count` needs. Second pass (mvcc met 3b's two requests): `ctxErr err` from `rangeResOwn`'s
`.ctxErr`, which now gives 3e's `Mvcc.rangeCtxErr err` (`ctxErr_of_range`; its `_ne_nil`, `_fresh`
give `ctxErr_not_errIs`; the old `context.isCtxErr err` was false: `rangeKeys` wraps `ctx.Err()` with
`fmt.Errorf`), and `rrOwn`'s `kvFits` from `kvsFit` (`kvSortOk` bounds the revisions, the version and
the lease).
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

/-- `executeRange(ctx, lg, tx, r, wtc)` on an open transaction `k`: the view's revision error, or the
reply `rangeOut` at the view's revision, or the context's error. -/
def executeRange.spec : Prop :=
  ∀ (ctx : GoInterface) (lg : Loc) (tx : GoInterface) (γ : Mvcc.MvccName) (tr : Loc) (k : Mvcc.MTxn)
    (r : Loc) (dq : DFrac) (rm : RangeReq) (wtc : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ Zap.isLogger lg ∗ TraceUtil.ctxTraceIs ctx (some tr) ∗
      TraceUtil.traceOwn tr ∗ Mvcc.mvccTxn tx γ tr k ∗ rangeReqOwn r dq rm ∗ ⌜targetOk rm⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.executeRange)) (Val #ctx)) (Val #lg)) (Val #tx)) (Val #r)) (Val #wtc))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); TraceUtil.traceOwn tr ∗
      Mvcc.mvccTxn tx γ tr k ∗ rangeReqOwn r dq rm ∗
      ((∃ e : EtcdErr, ⌜viewErr k rm.revision = some e ∧ resp = null⌝ ∗ errIs err e) ∨
       (⌜viewErr k rm.revision = none ∧ err = GoInterface.nil⌝ ∗ ∃ all : List KV,
          ⌜(viewStore k rm.revision).rangeKVs rm.range all⌝ ∗
          rangeOk resp (viewRev k) (rangeOut rm wtc all)) ∨
       (⌜resp = null ∧ rm.countOnly = false⌝ ∗ Context.ctxDone ctx ∗ ctxErr err)) }}

end spec
end Txn
end EtcdGrove
end Perennial
