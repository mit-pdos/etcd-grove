/-
## `Range(ctx, lg, kv, r, withTotalCount)` (`range.go`)

**Users.** The request path: `EtcdServer.Range` (`v3_server.go:149`, `withTotalCount` true, inside
`doSerialize`), `rangeStream` (`v3_server.go:199` count-only, `:223` each page, `false`); the apply
thread's `applierV3backend.Range` (`apply/backend.go:59`, `true`, `context.TODO()`). Snippets:
`examples/specreq/txn/read.go` (`ReqRangeLimitCount`, `ReqRangePinnedRev`, `ReqRangeStreamPages`,
`ReqRangeSortedKeysOnly`).

**Proof sketch.** `EnsureTrace` (4b's `EnsureTrace.spec`: the context's non-empty trace, whose ownership the caller
lends through `ctxTraceOwn o`, or a fresh one: `traceBack o tr` after). `kv.Read(ConcurrentReadTxMode, trace)` (3e's `KV.Read.contract`,
through `isMvcc`'s `shapes`: the reader token, the trace; the caller's update fired at the state `σ`
the transaction begins at, `Q σ` kept; `mvccTxn tx γ tr (.read σ)`). `executeRange` (its spec at
`.read σ`: `viewErr (.read σ) rm.revision` is `rm.revErr σ.kv` and `viewStore` is
`σ.kv.storeAt (rm.readRev σ.kv)`, by 3e's `mvccTxn_state`: `σ.kv.compacted ≤ σ.rev`). `txnRead.End()`
(3e: the reader token back). The deferred `RangeSecObserve` (returns).

**Changes.** The old spec (`specs-ref`'s `Range.lean`: `readAU` over mvcc's log, `rangeResult`, a
never-done context premise `nd`) restated over W0's history and answer, made a function
(`rangeOut`, `goSort`), the context's error an outcome. Round 1 (review `3b-review-1.md`): over 3e's API (`MvccState`, `isMvcc`, `mvccReaders γ 1` for the
thread token, the caller's trace lent and given back: F4), the answer at `σ.kv`. Integration
(I5): the context's error only for a full read (`rm.countOnly = false`, from `executeRange`), which
`Count` needs to exclude it.

**Margin.** The response's header carries only the revision. A cancelled context is reported only
if mvcc's per-key loop sees it (a full read).
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

/-- **`Range(ctx, lg, kv, r, withTotalCount)`**: one read transaction of the store `γ`, at the state
`σ` the caller's update fires at (when the read begins): mvcc's revision error (`revErr`), or the
answer `rangeOut` from the range's present keys at the revision read, header revision `σ.rev`; or,
once the context is done, its error. -/
def Range.spec : Prop :=
  ∀ (ctx : GoInterface) (o : Option Loc) (lg : Loc) (kv : GoInterface) (γ : Mvcc.MvccName) (r : Loc)
    (dq : DFrac) (rm : RangeReq) (wtc : Bool) (Q : Mvcc.MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ TraceUtil.ctxTraceIs ctx o ∗ ctxTraceOwn o ∗ Zap.isLogger lg ∗
      Mvcc.isMvcc kv γ ∗ Mvcc.mvccReaders γ 1 ∗ rangeReqOwn r dq rm ∗ ⌜targetOk rm⌝ ∗
      AU <{ ∃∃ (σ : Mvcc.MvccState), Mvcc.mvccState γ σ }> @ ⊤ \ ↑Mvcc.mvccN, ∅
        <{ Mvcc.mvccState γ σ, COMM Q σ }> }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.Range)) (Val #ctx)) (Val #lg)) (Val #kv)) (Val #r)) (Val #wtc))
  {{ (resp tr : Loc) (err : GoInterface), RET (PairV (PairV #resp #tr) #err);
      Mvcc.mvccReaders γ 1 ∗ rangeReqOwn r dq rm ∗ traceBack o tr ∗ ∃ σ : Mvcc.MvccState, Q σ ∗
      ((∃ e : EtcdErr, ⌜rm.revErr σ.kv = some e ∧ resp = null⌝ ∗ errIs err e) ∨
       (⌜rm.revErr σ.kv = none ∧ err = GoInterface.nil⌝ ∗ ∃ all : List KV,
          ⌜(σ.kv.storeAt (rm.readRev σ.kv)).rangeKVs rm.range all⌝ ∗
          rangeOk resp σ.kv.rev (rangeOut rm wtc all)) ∨
       (⌜rm.revErr σ.kv = none ∧ resp = null ∧ rm.countOnly = false⌝ ∗ Context.ctxDone ctx ∗ ctxErr err)) }}

end spec
end Txn
end EtcdGrove
end Perennial
