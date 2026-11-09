/-
## `traceutil.EnsureTrace(ctx, lg, op, fields...)`

**Users.** The request path (`v3_server.go:118,169,341,391`: grpc's per-call context, which carries
no trace), `txn.Range`/`Put`/`DeleteRange`/`Txn` (`txn/*.go`: the request's context, carrying the
request's non-empty trace, or `context.TODO()` on the apply thread), the applier's `Compaction`
(`apply/backend.go:69`, `TODO()`), the read loop (`read/read.go:109`, `Background()`). Snippets:
`trace.go` (`ReqRequestTrace`, `ReqApplyTraceHandoff`, `ReqReadLoopTrace`).

**Proof sketch.** `Get(ctx)` (`Get.spec`); `IsEmpty()` (`traceEmpty`, persistent: readable whoever
owns the trace); a context's non-empty trace: `(ctx, t0)`, nothing else touched (the fields are not
used). Otherwise `newTrace` (`newTrace.spec`) and `context.WithValue(ctx, TraceKey{}, t)` (W0's
`Context.WithValue.spec`: `TraceKey` is an empty struct, comparable), which gives `ctxOk`,
`ctxWithValues` and `ctxValueAt`; `ctxTraceIs ctx' (some t)` is `WithValue`'s value at its own key
(the realization: `valueCtx.Value`'s body returns `t` at `TraceKey{}`).

**Changes.** From `specs-ref`'s `EnsureTrace.lean`: the input context is any `Context.ctxOk` (was
the mvcc's `txnCtx` descriptor); the other packages' facts about the new context (grpc's incoming
metadata, otel's span) are no longer listed one by one: the post gives W0's `ctxWithValues` and
`ctxValueAt` at `traceKey`, from which each package's "a value at another key" law carries its own
fact (`Context.ctxNoMeta_value`, `ctxTraceIs_value`, `OtelTrace.ctxSpanOk_value`). The context's
trace's ownership is no longer taken: only its emptiness is read.

**Margin.** In the reuse case the fields are not stored (their slice is dropped).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceUtil

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- **A context carrying a non-empty trace, and that trace**: `ctx` and its own trace if it carries
a non-empty one; else a new trace, the caller's, in a `WithValue` of `ctx`. -/
def EnsureTrace.spec : Prop :=
  ∀ (ctx : GoInterface) (o : Option Loc) (e : Bool) (lg : Loc) (op : GoString) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ Context.ctxOk ctx ∗ ctxTraceIs ctx o ∗
      (match o with | some t0 => traceEmpty t0 e | none => iprop(True)) ∗
      fieldsOwn fields ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace)) (Val #ctx))
      (Val #lg)) (Val #op)) (Val #fields))
  {{ (ctx' : GoInterface) (t : Loc), RET (PairV #ctx' #t);
      Context.ctxOk ctx' ∗ ctxTraceIs ctx' (some t) ∗ traceEmpty t false ∗
      match o, e with
      | some t0, false => iprop(⌜ctx' = ctx ∧ t = t0⌝)
      | _, _ => iprop(traceOwn t ∗ Context.ctxWithValues ctx ctx' ∗
          Context.ctxValueAt ctx ctx' traceKey) }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
