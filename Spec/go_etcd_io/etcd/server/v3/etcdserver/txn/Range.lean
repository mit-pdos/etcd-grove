/-
## `Range(ctx, lg, kv, r, withTotalCount)` (`range.go`)

**Users.** The request path: `EtcdServer.Range` (`v3_server.go:149`, `withTotalCount` true, inside
`doSerialize`), `rangeStream` (`v3_server.go:199` count-only, `:223` each page, `false`); the apply
thread's `applierV3backend.Range` (`apply/backend.go:59`, `true`, a context never done). Snippets:
`examples/specreq/txn/read.go` (`ReqRangeAtRev`, `ReqRangePinnedCompacted`, `ReqRangeStreamPages`).

**Proof sketch.** `EnsureTrace` (4b: a trace, `traceAt`). `kv.Read(ConcurrentReadTxMode, trace)`
(3e's `Read`: takes the thread token for the store's reader lock, fires the caller's update at the
state `h` it begins at, gives `mvccTxn tx γ .read h []`; `Q h` is kept for the post).
`executeRange` (its spec at kind `.read`, `evs = []`: `viewErr h [] rm.revision` is `rm.revErr h`,
`viewRev h [] = h.rev`, `viewStore h [] rm.revision` is `h.storeAt (rm.readRev h)` below the
revision and the current store at or above it; the error cases are the same). `txnRead.End()` (3e:
the thread token back). The deferred `RangeSecObserve` (its spec: returns).

**Changes.** The old spec (`specs-ref`'s `Range.lean`: `readAU` over mvcc's `MvccState` log,
`rangeResult` over the log, `mvccReaders γ 1`, a never-done context premise `nd` for one
conclusion) restated over W0's history (`KVHist`) and W0's answer, made a function (`rangeOut`:
unique, `goSort`), with the context's error an outcome (any context: the request path's may be
cancelled), the reader slot a thread token (bounds plan), the trace a `traceAt`.

**Margin.** The response's header carries only the revision (the gRPC layer fills the rest). A
cancelled context is reported only if mvcc's per-key loop sees it (the non-keys-only path).
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

/-- **`Range(ctx, lg, kv, r, withTotalCount)`**: one read transaction of the store `γ`, at the state
`h` the caller's update fires at (when the read begins): mvcc's revision error (`revErr`), or the
answer `rangeOut` from the range's present keys at the revision read, header revision `h.rev`;
or, once the context is done, its error. -/
def Range.spec : Prop :=
  ∀ (ctx : GoInterface) (lg : Loc) (kv : GoInterface) (γ : MvccName) (r : Loc) (dq : DFrac)
    (rm : RangeReq) (wtc : Bool) (Q : KVHist → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Context.ctxOk ctx ∗ Zap.isLogger lg ∗ mvccKV kv γ ∗ threadTok ∗
      rangeReqOwn r dq rm ∗ ⌜targetOk rm⌝ ∗
      AU <{ ∃∃ (h : KVHist), mvccState γ h }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState γ h, COMM Q h }> }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.Range)) (Val #ctx)) (Val #lg)) (Val #kv)) (Val #r)) (Val #wtc))
  {{ (resp tr : Loc) (err : GoInterface), RET (PairV (PairV #resp #tr) #err);
      threadTok ∗ rangeReqOwn r dq rm ∗ traceAt tr ∗ ∃ h : KVHist, Q h ∗
      ((∃ e : EtcdErr, ⌜rm.revErr h = some e ∧ resp = null⌝ ∗ errIs err e) ∨
       (⌜rm.revErr h = none ∧ err = GoInterface.nil⌝ ∗ ∃ all : List KV,
          ⌜(h.storeAt (rm.readRev h)).rangeKVs rm.range all⌝ ∗ rangeOk resp h.rev (rangeOut rm wtc all)) ∨
       (⌜rm.revErr h = none ∧ resp = null⌝ ∗ Context.ctxDone ctx ∗ ctxErr err)) }}

end spec
end Txn
end EtcdGrove
end Perennial
