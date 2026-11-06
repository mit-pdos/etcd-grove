/-
`trace.SpanFromContext`: the trust boundary (`go.opentelemetry.io/otel/trace` is names-only).
Lean-first (no Rocq counterpart). mvcc's `watchStream.Watch` takes the span of its context and
ends it when the watcher is cancelled (`defer span.End()` in the cancel closure it stores).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import GeneratedProof.go_opentelemetry_io.otel.trace
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

/-- `sp` is a `trace.Span` (persistent): a non-nil interface value whose `End()` returns
(tracing has no effect here): `End(opts...)` (`options ...SpanEndOption`; `span.End()`, deferred
in `Watch`'s cancel closure and the server's request path, passes the nil slice) and (2026-10-12,
the server's request path) `AddEvent(name, opts...)` and `RecordError(err, opts...)`. -/
def trace.isSpan (sp : GoInterface) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜sp = GoInterface.ok si⌝ ∗
    □ (∀ (opts : GoSlice),
      {{ True }} (App (Val #(methods si.ty go!"End" si.v)) (Val #opts)) {{ RET #(); True }}) ∗
    □ (∀ (name : GoString) (opts : GoSlice),
      {{ True }} (App (App (Val #(methods si.ty go!"AddEvent" si.v)) (Val #name)) (Val #opts))
      {{ RET #(); True }}) ∗
    □ (∀ (err : GoInterface) (opts : GoSlice),
      {{ True }} (App (App (Val #(methods si.ty go!"RecordError" si.v)) (Val #err)) (Val #opts))
      {{ RET #(); True }}))

instance trace.isSpan_persistent (sp : GoInterface) : Persistent (trace.isSpan (GF := GF) sp) := by
  unfold trace.isSpan; infer_instance

/-- `context.TODO()`'s value: a `todoCtx{}` as a `Context` (`Spec/context/TODO.lean`; mvcc's
`todoCtxV`, the cache's `todoCtxVal`). Its `Done()` is `nil`, so it is not an `isContext`. -/
abbrev trace.todoCtx : GoInterfaceOk :=
  interface.mk context.todoCtx.ty #(zero_val context.todoCtx)

/-- `trace.SpanFromContext(ctx)` (a context, or `context.TODO()`) returns a span. (2026-11-06, the
user: weakened to admit `context.TODO()`, which the mvcc tester's `Watch` passes.) Faithful:
otel's `SpanFromContext` only calls `ctx.Value(currentSpanKey)` (`trace/context.go`); a context
answers it (`isContext`'s `Value`), and `context.TODO()` answers `nil`, for which the function
returns the no-op span (`noopSpanInstance`), whose `End`, `AddEvent` and `RecordError` return. -/
abbrev trace.SpanFromContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.trace ∗
      (⌜ctx = trace.todoCtx⌝ ∨ context.isContext ctx cd) }}
    (App (Val (@! trace.SpanFromContext)) (Val #(GoInterface.ok ctx)))
  {{ (sp : GoInterface), RET #sp; trace.isSpan sp }}

end spec

end EtcdGrove
end Perennial
