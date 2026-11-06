/-
The vocabulary of `go.opentelemetry.io/otel/trace` (names-only): a span (`trace.isSpan`), a span
a context may carry (`trace.isParentSpan`: also what otel's tracers call on it), a context whose
span, under otel's key, is one (`trace.spanCtxOk`) and one with no span (`trace.spanCtxNone`). A module of its own, light, so
that grpc's run context (`grpcRunCtx`, `Proof/google_golang_org/grpc/InvGrpc.lean`) can state it.
Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.go_opentelemetry_io.otel.trace
public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_opentelemetry_io.otel

section defs
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

/-- **`sp` is a span a context may carry** (persistent; 2026-11-06, the fix of
`traceutil.Tracer.Start`'s axiom, `notes/axiom-review/otel-spanfromcontext-todo.md`): a span
(`trace.isSpan`) whose `SpanContext()` and `IsRecording()` also return, the methods otel's
tracers call on the span of the context they are given (v1.47.0): `noop.Tracer.Start`
(`trace/noop/noop.go`, etcd's `traceutil.Tracer`) calls `SpanContext()` and, on a non-zero span
context, `IsRecording()`, and returns that span itself, with the context, when it is not
recording; the SDK's `tracer.Start` (`sdk/trace/tracer.go`) calls `SpanContext()`
(`SpanContextFromContext`, in `newSpan` and in its sampler). `SpanContext` is a struct of
unexported fields (any value: `Equal` and `IsValid` compare them). -/
def trace.isParentSpan (sp : GoInterface) : IProp GF :=
  iprop(trace.isSpan sp ∗ ∃ si : GoInterfaceOk, ⌜sp = GoInterface.ok si⌝ ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"SpanContext" si.v)) (Val #()))
      {{ (sc : trace.SpanContext), RET #sc; True }}) ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"IsRecording" si.v)) (Val #()))
      {{ (b : Bool), RET #b; True }}))

instance trace.isParentSpan_persistent (sp : GoInterface) :
    Persistent (trace.isParentSpan (GF := GF) sp) := by
  unfold trace.isParentSpan; infer_instance

theorem trace.isSpan_of_parent (sp : GoInterface) :
    trace.isParentSpan (GF := GF) sp ⊢ trace.isSpan sp := by
  unfold trace.isParentSpan
  iintro ⟨H, -⟩
  iexact H

/-- otel's span key `currentSpanKey` as an `any` (`trace/context.go`: `type traceContextKeyType int`,
`const currentSpanKey traceContextKeyType = iota`, unexported; `ContextWithSpan(parent, span)` is
`context.WithValue(parent, currentSpanKey, span)`, and `SpanFromContext(ctx)` reads
`ctx.Value(currentSpanKey)`). -/
abbrev trace.spanKeyVal : GoInterface :=
  interface.mkOk trace.traceContextKeyType.ty #(W64 0)

/-- **The context `ctx`'s span is a span** (persistent; 2026-11-06, the fix of
`notes/axiom-review/otel-spanfromcontext-todo.md`): its `Value(currentSpanKey)`, from any
goroutine, returns `nil` or a span (`trace.isParentSpan`, since 2026-11-06 with
`traceutil.Tracer.Start`'s fix: a span whose `SpanContext()` and `IsRecording()` also return,
which otel's tracers call on it). Through a pure property `R` of the result
(the value returned satisfies `R`, and every value satisfying `R` is `nil` or a span), so that a
context's laws stated for pure properties (`context.WithValue`'s delegation to its parent at
another key) carry it. What `trace.SpanFromContext` needs of a context (it returns the value
when it is a `Span`, else the no-op span); `context.isContext` says nothing of keys other than
`&cancelCtxKey`, so a context of the program's own could answer otel's key with a span whose
`End` panics. -/
def trace.spanCtxOk (ctx : GoInterfaceOk) : IProp GF :=
  iprop(∃ R : GoInterface → Prop,
    □ (∀ v : GoInterface, ⌜R v⌝ -∗ (⌜v = GoInterface.nil⌝ ∨ trace.isParentSpan v)) ∗
    □ ({{ True }} (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #trace.spanKeyVal))
      {{ (v : GoInterface), RET #v; ⌜R v⌝ }}))

instance trace.spanCtxOk_persistent (ctx : GoInterfaceOk) :
    Persistent (trace.spanCtxOk (GF := GF) ctx) := by
  unfold trace.spanCtxOk; infer_instance

/-- **The context `ctx` carries no span** (persistent; 2026-11-06): its `Value(currentSpanKey)`
returns `nil`. `context.Background()`'s and `TODO()`'s, and their children at other keys'
(`Proof/go_opentelemetry_io/otel/trace/SpanCtxLaws.lean`); it gives `trace.spanCtxOk`
(`spanCtxOk_of_nil`). What k8s's `tracing.Start` takes (`Spec/k8s_io/component_base/tracing/
Start.lean`): on it, `SpanFromContext` is the no-op span, whose `TracerProvider()` is the no-op
one. -/
def trace.spanCtxNone (ctx : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #trace.spanKeyVal))
      {{ RET #GoInterface.nil; True }}))

instance trace.spanCtxNone_persistent (ctx : GoInterfaceOk) :
    Persistent (trace.spanCtxNone (GF := GF) ctx) := by
  unfold trace.spanCtxNone; infer_instance

end defs

end EtcdGrove
end Perennial
