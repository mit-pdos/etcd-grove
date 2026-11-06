/-
The vocabulary of `k8s.io/component-base/tracing` (names-only; 2026-11-06, the fix of its axioms,
found false with otel's `trace.SpanFromContext`, `notes/axiom-review/otel-spanfromcontext-todo.md`;
the user approved fixing axioms as needed): a span (`tracing.isSpan`, what `SpanFromContext` and
`Start` return and `Span.End`/`Span.AddEvent` take, in place of `⌜sp ≠ null⌝`: a program can
allocate a `tracing.Span{}`, whose nil `otelSpan` makes `End` panic), and the contexts the two
accept (`tracing.ctxSpansOk`, `tracing.startCtxOk`). Lean-first (no Rocq counterpart).

`tracing.go` (component-base `cd2c1afd246a`, otel v1.47.0, k8s.io/utils `be93311217bd`):

```go
func SpanFromContext(ctx context.Context) *Span {
	return &Span{otelSpan: trace.SpanFromContext(ctx), utilSpan: utiltrace.FromContext(ctx)}
}
func Start(ctx context.Context, name string, attributes ...attribute.KeyValue) (context.Context, *Span) {
	ctx, otelSpan := trace.SpanFromContext(ctx).TracerProvider().Tracer(instrumentationScope).Start(ctx, name, trace.WithAttributes(attributes...))
	utilSpan := utiltrace.FromContext(ctx).Nest(name, attributesToFields(attributes)...)
	return utiltrace.ContextWithTrace(ctx, utilSpan), &Span{otelSpan: otelSpan, utilSpan: utilSpan}
}
func (s *Span) AddEvent(name string, attributes ...attribute.KeyValue) {
	s.otelSpan.AddEvent(name, trace.WithAttributes(attributes...))
	if s.utilSpan != nil { s.utilSpan.Step(name, attributesToFields(attributes)...) }
}
func (s *Span) End(logThreshold time.Duration) {
	s.otelSpan.End()
	if s.utilSpan != nil { s.utilSpan.LogIfLong(logThreshold) }
}
```

`utiltrace.FromContext(ctx)` is `ctx.Value(ContextTraceKey{}).(*Trace)` (or `nil`): it calls
`Value` on `ctx` (a `nil` `ctx` panics). A `*Trace`'s `Nest`, `Step` and `LogIfLong` return for
every `*Trace` a program can make (its fields are unexported: `New`/`Nest`'s, or the zero value):
they lock its `RWMutex`, append, and format through `fmt` (which recovers a panicking `String`)
and `klog`.
-/
module

public import Proof.go_opentelemetry_io.otel.trace.SpanCtxLaws
public import GeneratedProof.k8s_io.component_base.tracing
public import GeneratedProof.k8s_io.utils.trace

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- k8s.io/utils' trace key `utiltrace.ContextTraceKey{}` as an `any`. -/
abbrev tracing.utilTraceKeyVal : GoInterface :=
  interface.mkOk k8s_io.utils.trace.ContextTraceKey.ty
    #(zero_val k8s_io.utils.trace.ContextTraceKey)

/-- **`sp` is a span** (persistent): its `End(d)` and `AddEvent(name, attrs...)` return. True of
the spans `tracing.SpanFromContext` and `tracing.Start` return (their specs): an otel span
(`trace.isSpan`: its `End` and `AddEvent` return) and a `*utiltrace.Trace` or `nil` (see the file
header). -/
def tracing.isSpan (sp : Loc) : IProp GF :=
  iprop(□ (∀ d : time.Duration,
      {{ True }} (App (Val (sp @!! go.GoType.PointerType k8s_io.component_base.tracing.Span.ty @!!
        go!"End")) (Val #d)) {{ RET #(); True }}) ∗
    □ (∀ (name : GoString) (attrs : GoSlice),
      {{ True }} (App (App (Val (sp @!! go.GoType.PointerType k8s_io.component_base.tracing.Span.ty @!!
        go!"AddEvent")) (Val #name)) (Val #attrs)) {{ RET #(); True }}))

instance tracing.isSpan_persistent (sp : Loc) : Persistent (tracing.isSpan (GF := GF) sp) := by
  unfold tracing.isSpan; infer_instance

/-- **The context `ci`'s utiltrace key answers** (persistent): its `Value(utiltrace.ContextTraceKey{})`
returns (what `utiltrace.FromContext` calls; any value: a `*Trace` it holds is one of
`utiltrace`'s, see the file header). `context.isContext` says nothing of keys other than
`&cancelCtxKey`. -/
def tracing.utilTraceCtxOk (ci : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods ci.ty go!"Value" ci.v)) (Val #tracing.utilTraceKeyVal))
    {{ (v : GoInterface), RET #v; True }}))

instance tracing.utilTraceCtxOk_persistent (ci : GoInterfaceOk) :
    Persistent (tracing.utilTraceCtxOk (GF := GF) ci) := by
  unfold tracing.utilTraceCtxOk; infer_instance

/-- **A context `tracing.SpanFromContext` accepts** (persistent): non-nil, its span a span
(`trace.spanCtxOk`: `Value(currentSpanKey)` returns `nil` or a span, which `End` and `AddEvent`
call), and its utiltrace key answering (`tracing.utilTraceCtxOk`). -/
def tracing.ctxSpansOk (ctx : GoInterface) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜ctx = GoInterface.ok ci⌝ ∗ trace.spanCtxOk ci ∗
    tracing.utilTraceCtxOk ci)

instance tracing.ctxSpansOk_persistent (ctx : GoInterface) :
    Persistent (tracing.ctxSpansOk (GF := GF) ctx) := by
  unfold tracing.ctxSpansOk; infer_instance

/-- **A context `tracing.Start` accepts** (persistent): one with no span (`trace.spanCtxNone`: then
`trace.SpanFromContext(ctx)` is otel's no-op span, whose `TracerProvider()` is the no-op provider,
whose tracer's `Start` reads only `ctx`'s span; a span of the context's own would have its
`TracerProvider()` called, which `trace.isParentSpan` does not cover), and its utiltrace key
answering (`tracing.utilTraceCtxOk`, which `ContextWithSpan`'s child delegates to). -/
def tracing.startCtxOk (ci : GoInterfaceOk) : IProp GF :=
  iprop(trace.spanCtxNone ci ∗ tracing.utilTraceCtxOk ci)

instance tracing.startCtxOk_persistent (ci : GoInterfaceOk) :
    Persistent (tracing.startCtxOk (GF := GF) ci) := by
  unfold tracing.startCtxOk; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- **`context.Background()` holds no trace**: its `Value` (promoted from `emptyCtx`) returns
`nil`. -/
theorem tracing.utilTraceCtxOk_background :
    ⊢ tracing.utilTraceCtxOk (GF := GF) _root_.Perennial.context.backgroundCtxVal := by
  unfold tracing.utilTraceCtxOk
  imodintro
  wp_start
  wp_method_call
  wp_auto
  iapply HΦ
  itrivial

/-- **`tracing.Start` accepts `context.Background()`.** -/
theorem tracing.startCtxOk_background :
    ⊢ tracing.startCtxOk (GF := GF) _root_.Perennial.context.backgroundCtxVal := by
  unfold tracing.startCtxOk
  isplitl
  · iapply trace.spanCtxNone_background
  · iapply tracing.utilTraceCtxOk_background

/-- **A context `tracing.Start` accepts, `tracing.SpanFromContext` does.** -/
theorem tracing.ctxSpansOk_of_start (ci : GoInterfaceOk) :
    tracing.startCtxOk (GF := GF) ci ⊢ tracing.ctxSpansOk (GoInterface.ok ci) := by
  unfold tracing.startCtxOk tracing.ctxSpansOk
  iintro ⟨#Hn, #Hu⟩
  iexists ci
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply trace.spanCtxOk_of_nil; iexact Hn
  · iexact Hu

end lemmas

end EtcdGrove
end Perennial
