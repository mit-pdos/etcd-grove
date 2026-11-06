# `trace.SpanFromContext.wp_proof` (admits `context.TODO()`): the weakening survives, the `isContext` arm falls (Go side)

**Reviewed** 2026-11-06, at `mvcc-api` `b4bc6a538c` (otel `go.opentelemetry.io/otel/trace`
v1.47.0, the etcd fork's `server/go.mod`; etcd fork `ce3dbc097f`; go1.27.3), by the `axiom` skill.
Not on a branch: the caller asked for no commit and no `lake` run. The Go counterexample is in the
worktree, uncommitted: `examples/axiomcx/spanctx/{spanctx.go,spanctx_test.go}` (inlined below).

## The axiom

`trace.SpanFromContext.wp_proof` (`Proof/go_opentelemetry_io/otel/trace/SpanFromContext.lean`),
its triple `trace.SpanFromContext.spec` (`Spec/go_opentelemetry_io/otel/trace/SpanFromContext.lean`):

```lean
∀ ctx cd, {{ isPkgInit otel/trace ∗ (⌜ctx = trace.todoCtx⌝ ∨ context.isContext ctx cd) }}
  trace.SpanFromContext (ok ctx) {{ sp, RET #sp; trace.isSpan sp }}
```

`trace.isSpan sp`: `sp` a non-nil interface whose `End(opts)`, `AddEvent(name, opts)` and
`RecordError(err, opts)` return (`{{ True }} … {{ RET #(); True }}`), persistently. `b4bc6a538c`
added the disjunct `⌜ctx = trace.todoCtx⌝` (`trace.todoCtx := interface.mk context.todoCtx.ty
#(zero_val context.todoCtx)`); the `isContext` arm was there before (`notes/audit.md`: "ok, the
context's span or a noop span"). Reviewed with it: Perennial's `context.isContextDef`
(`Perennial/Proof/context/Base.lean:481-509`), `wp_WithCancel_gen`, `isContext_cancelCtx_of` and
`wp_parentCancelCtx_self_of` (`Perennial/Proof/context/{WithCancelGen,CancelCtxContext}.lean`),
`Spec/context/TODO.lean`, the only caller of the new arm (`WatchStream.Watch.contract`,
`Spec/.../storage/mvcc/Api.lean:692`).

## The Go code

`trace/context.go:37-45`:

```go
func SpanFromContext(ctx context.Context) Span {
	if ctx == nil { return noopSpanInstance }
	if span, ok := ctx.Value(currentSpanKey).(Span); ok { return span }
	return noopSpanInstance
}
```

`noopSpanInstance` is `noopSpan{}` (`noop.go:52`), whose `End`, `AddEvent`, `RecordError` are empty
(`noop.go:70-76`). `currentSpanKey` is an unexported `traceContextKeyType` (an `int`); the only
exported setter is `ContextWithSpan(parent, span)` = `context.WithValue(parent, currentSpanKey,
span)`. `Span` embeds `embedded.Span`, an exported interface, so any package can implement `Span`
(embedding `trace.Span` or `embedded.Span`) with its own `End`.

go1.27.3 `context/context.go:182-226`: `TODO()` returns `todoCtx{}`, `type todoCtx struct{ emptyCtx }`,
and `emptyCtx.Value` returns `nil`.

## Verdict

- **The weakening (the `todoCtx` arm): survives.** `todoCtx{}`'s `Value(currentSpanKey)` is `nil`,
  the type assertion fails, the result is `noopSpanInstance`, a non-nil `noopSpan` whose three
  methods return. `trace.todoCtx` is the value `context.TODO()`'s spec returns (`todoCtxVal`, the
  same `interface.mk context.todoCtx.ty #(zero_val context.todoCtx)`), and Go code outside
  `context` cannot build another `todoCtx` (unexported), nor would it behave differently.
  `isPkgInit` covers `noopSpanInstance`'s initializer.
- **The `isContext` arm: refuted on the Go side** (Lean proof not built: no `lake` in this
  session). The axiom's argument, "a context answers it (`isContext`'s `Value`)", is wrong:
  `isContextDef`'s `"#HValue"` specifies `Value` only at context's own key `&cancelCtxKey`
  (`cancelCtxKeyAny`; the docstring: "the `Values` field of `ContextDesc` is unused"), and
  `isContext` is not sealed, so a program can prove it of its own `Context` type, whose `Value`
  answers `currentSpanKey` with a span whose `End` panics. The same root as
  [outgoingOf-noValues](outgoingOf-noValues.md) (`isContext` says nothing of other keys).

## The counterexample

```go
package spanctx

import ("context"; "go.opentelemetry.io/otel/trace")

type badSpan struct{ trace.Span }                 // a trace.Span; the embedded interface supplies the rest
func (badSpan) End(...trace.SpanEndOption) { panic("badSpan.End") }

type spanCtx struct{ context.Context }            // Deadline/Done/Err promoted from a *cancelCtx
func (c spanCtx) Value(k any) any {
	if _, ok := k.(*int); ok { return c.Context.Value(k) }   // &cancelCtxKey is a *int
	return badSpan{}                                          // every other key, currentSpanKey included
}

func Main() {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	sp := trace.SpanFromContext(spanCtx{ctx})
	sp.End()
}
```

`GOTOOLCHAIN=go1.27.3 go test -v ./axiomcx/spanctx/` (in `examples/`, otel v1.47.0):

```
=== RUN   TestMainPanics
    spanctx_test.go:8: recovered: badSpan.End
--- PASS: TestMainPanics (0.00s)
```

Deterministic: `Main` panics on every run.

**The proof (not built; its plan).** `{{ isPkgInit spanctx }} Main #() {{ RET #(); True }}` from
`trace.SpanFromContext.spec` and Perennial's proved `context` lemmas only:

1. `context.WithCancel(Background())` by `wp_WithCancel_gen` (`Results.lean:188`) with the background
   propagation (as `wp_WithCancel_Background_of` does): `isCancelCtxOf c γ True`, `ctxField c ↦□
   Background`, `cancelSpec cancel γ True`.
2. `isContext (spanCtx{ok c}) s` at the inner's descriptor `s` (`Done_gn := γ`, `PDone := True`,
   `Deadline := none`), clause by clause, each the inner's through the promoted method (one
   `wp_method_call` step, then the inner's clause from `isContext_cancelCtx_of`): `HDeadline`,
   `HDone`, `HErr`, `HErrDone`; `HValue` at `cancelCtxKeyAny`: the assertion `k.(*int)` succeeds
   (a concrete pointer type, decidable), then the inner's `Value`; `HDoneFresh`, `HClosedchan`: the
   inner's ghost facts, unchanged; `HParentCC`: `spanCtx`'s type is not `stopCtx`, and
   `parentCancelCtx(spanCtx{c})` is `wp_parentCancelCtx_self_of`'s proof with the wrapper's `Done`
   and `Value` (each one step from the inner's): it returns `(c, true)`.
3. `trace.SpanFromContext` by the axiom's `isContext` arm: `isSpan sp`; `sp.End()` by its `End`
   clause; the deferred `cancel()` by `cancelSpec` at `True`.

Expected `#print axioms`: `trace.SpanFromContext.wp_proof`, Lean's three and the generic ones. The
Goose translation of `spanCtx` (a struct embedding an interface, a promoted method set) and of
`badSpan` (embedding the names-only `trace.Span`) is untested.

## What rests on it

`grep -rn 'SpanFromContext.wp_proof'`: mvcc's `watchStream.Watch` (`Link.lean`, the new arm),
`EtcdServer.raftRequest` and `processInternalRaftRequestOnce` (the server's request path, contexts
from grpc's axioms), k8s `component_base/tracing.SpanFromContext` and the cacher's `Link.lean`. Every
closed program here applies it at `TODO()` or at contexts made by grpc's handler (otelgrpc's stats
handler stores SDK or no-op spans), where the claim is true; the false instances are contexts built
by the program itself. (`etc/tcb-report.py --roots` not run: it needs an up-to-date build.)

## Proposed restatement (not applied)

Keep the `todoCtx` arm; give the `isContext` arm a span fact for the span key, which the context's
maker supplies:

```lean
/-- `ctx`'s span, if any, is a span: `Value(currentSpanKey)` returns a value that is not a
`trace.Span`, or one that `isSpan`. -/
def trace.ctxSpanOk (ctx : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ Φ, ▷ (∀ v : GoInterface, (⌜¬ implementsSpan v⌝ ∨ trace.isSpan v) -∗ Φ #v) -∗
    WP (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #currentSpanKeyAny)) {{ Φ }})

{{ isPkgInit otel/trace ∗ (⌜ctx = trace.todoCtx⌝ ∨ (context.isContext ctx cd ∗ trace.ctxSpanOk ctx)) }}
  trace.SpanFromContext (ok ctx) {{ sp, RET #sp; trace.isSpan sp }}
```

with laws (true of Go's `context`: `*cancelCtx`, `*timerCtx` and `*valueCtx` at another key delegate
`Value` to the parent) carrying `ctxSpanOk` from `Background()`/`TODO()` to `WithCancel`,
`WithTimeout` and `WithValue` children, and grpc's server-side context axioms stating it of the
handler's context. Alternatively, an opaque `trace.ctxSpanOk ctx` given by those producers only.
Either is a change to a trusted statement: for the user.

## Not tried

The `isSpan` clauses' other methods (`AddEvent`, `RecordError`) at the no-op span: empty bodies, as
`End`. A `nil` `ctx` (the spec takes `GoInterface.ok ctx`: excluded).

## Superseded verdict (2026-11-06)

**2026-11-06, fixed (the user approved):** the `isContext` arm now also takes `trace.spanCtxOk ctx`
(`Value(currentSpanKey)` returns `nil` or a span), the review's restatement with `nil ∨ isSpan` in
place of "not a `Span` or `isSpan`"; `grpcRunCtx` and `traceutil.Tracer.Start`'s post supply it,
`Proof/go_opentelemetry_io/otel/trace/SpanCtxLaws.lean` proves it of `Background()`,
`WithCancel(Background())` and `WithValue` children (`notes/decisions.md`, "`trace.SpanFromContext`'s
`isContext` arm"). The counterexample's `spanCtx` has no `spanCtxOk`. Same root, open:
`traceutil.Tracer.Start`'s axiom (the no-op tracer returns `ctx`'s span, after calling its
`SpanContext()` and `IsRecording()`).

## Tracer.Start and k8s's tracing (2026-11-06, fixed; the user approved fixing axioms as needed)

Checked against otel v1.47.0 (`examples/go.mod`), k8s component-base `cd2c1afd246a` and k8s.io/utils
`be93311217bd` (`examples/k8setcd3/go.mod`).

- **`traceutil.Tracer.Start.wp_proof`: refuted on the Go side, same root.** etcd's `traceutil.Tracer`
  is `noop.NewTracerProvider().Tracer(...)`; `noop.Tracer.Start` (`trace/noop/noop.go:54-73`) calls
  `trace.SpanFromContext(ctx)`, then `span.SpanContext()` and, on a non-zero one,
  `span.IsRecording()`, returning `ctx, span` when it is not recording. A context answering
  `currentSpanKey` with a span whose `SpanContext` panics refutes the run's return; one whose
  `SpanContext` is non-zero, `IsRecording` false and `End` panicking refutes `isSpan sp`. (The SDK
  tracer, `sdk/trace/tracer.go`, also calls `SpanContext()`, through `SpanContextFromContext`.)
  **Fix:** premise `trace.spanCtxOk ctx`, whose span predicate is now `trace.isParentSpan` (`isSpan`
  plus `SpanContext()` and `IsRecording()` returning); post `trace.spanCtxOk ctx'`.
- **k8s `tracing.SpanFromContext.wp_proof`: refuted (no premise on `ctx`).** `SpanFromContext(nil)`
  panics in `utiltrace.FromContext` (`ctx.Value(ContextTraceKey{})` on a nil interface); a context
  of the program's own can panic in `Value`. Its post `⌜sp ≠ null⌝` with **`tracing.Span.End`/
  `AddEvent`** (`{{ ⌜sp ≠ null⌝ }} … {{ True }}`): `(&tracing.Span{}).End(0)` panics (nil
  `otelSpan`), so those two were false outright, and with a context holding a bad otel span so is
  the span `SpanFromContext` returns. **Fix:** `tracing.isSpan sp` (`End` and `AddEvent` return)
  in place of `⌜sp ≠ null⌝`, premise `tracing.ctxSpansOk ctx` (non-nil, `spanCtxOk`,
  `Value(ContextTraceKey{})` returning); `End`/`AddEvent` proved from `isSpan`.
- **k8s `tracing.Start.wp_proof`: refuted the same way** (`trace.SpanFromContext(ctx).TracerProvider()
  .Tracer(...).Start(ctx, ...)`, then `utiltrace.FromContext`). **Fix:** premise `tracing.startCtxOk ci`
  (no span, `trace.spanCtxNone`, so the provider is otel's no-op one; the utiltrace key answering),
  post `tracing.isSpan sp`.

Not built as counterexamples (Go-side reading only); the fixes' statements in
`notes/decisions.md`, "`traceutil.Tracer.Start` and k8s's `tracing` axioms".
