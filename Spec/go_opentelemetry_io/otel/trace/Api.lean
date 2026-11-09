/-
# OpenTelemetry's `trace` package: the trust boundary (batch 4b)

`go.opentelemetry.io/otel/trace` (and `otel/attribute`, `Spec/go_opentelemetry_io/otel/attribute/`)
are translated types and names only: their specs are **assumed**, true of otel's code at the pin.
etcd uses spans only to report: a request entry point starts one (`traceutil.Tracer.Start`, batch
4b's `TraceUtil.Tracer.Start.spec`) with attributes (`WithAttributes`, `attribute.String`, ...),
ends it (`defer span.End()`), records an error on it (`SpanFromContext(ctx).RecordError(err)`) or
an event (`AddEvent`). Nothing etcd computes depends on a span.

## Vocabulary

* `spanOk sp` (transparent, persistent: a bundle of an interface value's triples): `sp` is a
  `trace.Span` whose `End`, `RecordError` and `AddEvent` return. otel's spans are safe for
  concurrent use (the SDK's take their mutex; the no-op span does nothing).
* `ctxSpanOk ctx` (opaque, persistent): **the span context `ctx` carries** at otel's key
  (`currentSpanKey`, of type `traceContextKeyType`), if any, **is a genuine otel span**
  (`spanOk`), and `ctx.Value` at that key returns. The tracers call methods of that span
  (`SpanContext`, `IsRecording`), and `SpanFromContext` returns it; a program context whose value
  at otel's key were a span with a panicking method would refute both (`specs-ref`'s
  `notes/axiom-review/otel-spanfromcontext-todo.md`). Realization: the triple of
  `ctx.Value(currentSpanKey)`, returning `nil` or a value with `spanOk`.

## Laws

`ctxSpanOk_persistent`; `ctxSpanOk_background`, `ctxSpanOk_todo` (no span), `ctxSpanOk_child`
(a child carries its parent's), `ctxSpanOk_value` (a `WithValue` at a key of another type keeps it).
The tracer's `Start` gives it for the context it returns. A context made elsewhere (grpc's per-call
context: its `otelgrpc` stats handler puts an SDK or no-op span) is introduced by its maker (2a).
-/
module

public import GeneratedProof.go_opentelemetry_io.otel.trace
public import Spec.PkgInit.go_opentelemetry_io.otel.trace
public import Spec.context.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace OtelTrace

open Iris Iris.BI

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`sp` is a span whose `End`, `RecordError` and `AddEvent` return** (persistent bundle). -/
def spanOk (sp : GoInterface) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜sp = GoInterface.ok i⌝ ∗
    (□ ∀ (opts : GoSlice) (Φ : val → IProp GF), ▷ Φ #() -∗
      WP (App (Val #(methods i.ty go!"End" i.v)) (Val #opts)) {{ Φ }}) ∗
    (□ ∀ (err : GoInterface) (opts : GoSlice) (Φ : val → IProp GF), ▷ Φ #() -∗
      WP (App (App (Val #(methods i.ty go!"RecordError" i.v)) (Val #err)) (Val #opts)) {{ Φ }}) ∗
    (□ ∀ (name : GoString) (opts : GoSlice) (Φ : val → IProp GF), ▷ Φ #() -∗
      WP (App (App (Val #(methods i.ty go!"AddEvent" i.v)) (Val #name)) (Val #opts)) {{ Φ }}))

/-- **The span `ctx` carries, if any, is an otel span** (persistent; see the header). -/
opaque ctxSpanOk (ctx : GoInterface) : IProp GF := iprop(True)

end vocab

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def ctxSpanOk_persistent.spec : Prop := ∀ ctx, Persistent (ctxSpanOk (GF := GF) ctx)

def ctxSpanOk_background.spec : Prop :=
  ⊢ ctxSpanOk (GF := GF) (GoInterface.ok context.backgroundCtxVal)

def ctxSpanOk_todo.spec : Prop :=
  ⊢ ctxSpanOk (GF := GF) (GoInterface.ok context.todoCtxVal)

def ctxSpanOk_child.spec : Prop := ∀ ctx ctx',
  ctxSpanOk (GF := GF) ctx ∗ Context.ctxChild ctx ctx' ⊢ ctxSpanOk ctx'

def ctxSpanOk_value.spec : Prop := ∀ (ctx ctx' : GoInterface) (ki : GoInterfaceOk),
  ctxSpanOk (GF := GF) ctx ∗ Context.ctxValueAt ctx ctx' (GoInterface.ok ki) ∗
    ⌜ki.ty ≠ go_opentelemetry_io.otel.trace.traceContextKeyType.ty⌝ ⊢ ctxSpanOk ctx'

end laws

end OtelTrace
end EtcdGrove
end Perennial
