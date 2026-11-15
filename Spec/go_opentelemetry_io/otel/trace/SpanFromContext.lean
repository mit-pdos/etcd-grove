/-
`trace.SpanFromContext`: the trust boundary (`go.opentelemetry.io/otel/trace` is names-only).
Lean-first (no Rocq counterpart). mvcc's `watchStream.Watch` takes the span of its context and
ends it when the watcher is cancelled (`defer span.End()` in the cancel closure it stores).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import GeneratedProof.go_opentelemetry_io.otel.trace
public import Proof.go_opentelemetry_io.otel.trace.Defs
public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_opentelemetry_io.otel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `context.TODO()`'s value: a `todoCtx{}` as a `Context` (`Spec/context/TODO.lean`; mvcc's
`todoCtxV`, the cache's `todoCtxVal`). Its `Done()` is `nil`, so it is not an `isContext`. -/
abbrev trace.todoCtx : GoInterfaceOk :=
  interface.mk context.todoCtx.ty #(zero_val context.todoCtx)

/-- `trace.SpanFromContext(ctx)` (`context.TODO()`, or a context whose span is a span) returns a
span. (2026-11-06, the user: weakened to admit `context.TODO()`, which the mvcc tester's `Watch`
passes; then, the same day, the `isContext` arm found false and fixed, the user approving:
`notes/axiom-review/otel-spanfromcontext-todo.md`, it takes `trace.spanCtxOk ctx`.) Faithful:
otel's `SpanFromContext` (`trace/context.go`, v1.47.0) returns the no-op span `noopSpanInstance`
for a nil context (excluded: `ctx` is an `ok` interface), else calls `ctx.Value(currentSpanKey)`
once and returns its result if it is a `Span`, else `noopSpanInstance`. `noopSpanInstance` is
`noopSpan{}` (`noop.go`), whose `End`, `AddEvent` and `RecordError` are empty: a span
(`isPkgInit` covers its initializer). `context.TODO()` (`todoCtx{}`, whose promoted
`emptyCtx.Value` returns `nil`) gives it. Otherwise `trace.spanCtxOk ctx` says `Value(currentSpanKey)`
returns `nil` (not a `Span`: the no-op span) or a span (`isSpan`), which is returned. The
`isContext` arm alone (before the fix) was false: `isContext` specifies `Value` only at
`&cancelCtxKey`, and a program's own context type can answer otel's key with a span whose `End`
panics. (k8s 7f-4, Addendum T-g, Q2; decided by etcd-grove-81, 2026-11-12) The second arm is
`trace.spanCtxOk ctx` alone, without `isContext ctx cd`: `SpanFromContext` calls no other method of
`ctx` (`examples/premisefix/streamctx` `TestSpanFromContextValueOnly`: a context whose `Deadline`,
`Done` and `Err` panic works), and etcd's stream handlers pass a weak context (`srvCtxWeak`). The
binder `cd` is kept, unused. -/
abbrev trace.SpanFromContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.trace ∗
      (⌜ctx = trace.todoCtx⌝ ∨ trace.spanCtxOk ctx) }}
    (App (Val (@! trace.SpanFromContext)) (Val #(GoInterface.ok ctx)))
  {{ (sp : GoInterface), RET #sp; trace.isSpan sp }}

end spec

end EtcdGrove
end Perennial
