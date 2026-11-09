/-
The vocabulary of `go.opentelemetry.io/otel/trace` (names-only): a span (`trace.isSpan`) and a
context whose span, under otel's key, is one (`trace.spanCtxOk`). A module of its own, light, so
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

open Iris Iris.BI go_opentelemetry_io.otel

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

/-- otel's span key `currentSpanKey` as an `any` (`trace/context.go`: `type traceContextKeyType int`,
`const currentSpanKey traceContextKeyType = iota`, unexported; `ContextWithSpan(parent, span)` is
`context.WithValue(parent, currentSpanKey, span)`, and `SpanFromContext(ctx)` reads
`ctx.Value(currentSpanKey)`). -/
abbrev trace.spanKeyVal : GoInterface :=
  interface.mkOk trace.traceContextKeyType.ty #(W64 0)

/-- **The context `ctx`'s span is a span** (persistent; 2026-11-06, the fix of
`notes/axiom-review/otel-spanfromcontext-todo.md`): its `Value(currentSpanKey)`, from any
goroutine, returns `nil` or a span (`trace.isSpan`). Through a pure property `R` of the result
(the value returned satisfies `R`, and every value satisfying `R` is `nil` or a span), so that a
context's laws stated for pure properties (`context.WithValue`'s delegation to its parent at
another key) carry it. What `trace.SpanFromContext` needs of a context (it returns the value
when it is a `Span`, else the no-op span); `context.isContext` says nothing of keys other than
`&cancelCtxKey`, so a context of the program's own could answer otel's key with a span whose
`End` panics. -/
def trace.spanCtxOk (ctx : GoInterfaceOk) : IProp GF :=
  iprop(∃ R : GoInterface → Prop,
    □ (∀ v : GoInterface, ⌜R v⌝ -∗ (⌜v = GoInterface.nil⌝ ∨ trace.isSpan v)) ∗
    □ ({{ True }} (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #trace.spanKeyVal))
      {{ (v : GoInterface), RET #v; ⌜R v⌝ }}))

instance trace.spanCtxOk_persistent (ctx : GoInterfaceOk) :
    Persistent (trace.spanCtxOk (GF := GF) ctx) := by
  unfold trace.spanCtxOk; infer_instance

end defs

end EtcdGrove
end Perennial
