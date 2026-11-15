# The narrowing of `trace.otelSpan` (2026-11-13)

Decided by etcd-grove-81: the context sweep's minor (a), with (b) folded in
(`notes/ctx-sweep-fixes.md`, section 1, "Two smaller gaps"). A bug in this repository's trusted text,
not in the Go code.

## The refutation

`trace.otelSpan` (`Proof/context/LibKeys.lean`, opaque, trusted) admitted a span of any otel SDK
`TracerProvider`. The SDK's `tracer.Start(ctx, ...)` (sdk/trace v1.47.0 `tracer.go`, `Start` and
`newSpan`) passes the caller's `ctx` to the provider's configured components: the `Sampler`
(`ShouldSample(SamplingParameters{ParentContext: ctx})`), the `IDGenerator` (`NewIDs(ctx)`,
`NewSpanID(ctx, tid)`) and every registered `SpanProcessor.OnStart(ctx, span)`; and, when the tracer
was made with `OTEL_GO_X_OBSERVABILITY` set, the global `MeterProvider`'s instruments
(`internal/observ` `Tracer.SpanStarted(newCtx)`, `SpanLive(ctx)`, and `SpanEnded(origCtx)` in `End`:
`Enabled(ctx)`, `Add(ctx, ...)`). Any of them, if of the program's own, may read `ctx.Value(myKey{})`.
A context whose `Value` panics at `myKey{}` meets `k8sctx.k8sCtxOk` (it constrains only the audit,
utiltrace, runtime/trace, grpc and otel keys), so k8s's `tracing.Start` on a context holding such a
provider's span panics: `tracing.Start.spec` and the k8s store specs that take it were refutable.

The axiom review's scratch tests (`/shared/tmp/coord-81/ctxfix-review/k8sctx/review_test.go`,
`TestReviewSamplerReadsKey`, `TestReviewProcessorReadsKey`) show the panic for a sampler and a
processor. Reach: no closed theorem's real context (they start from `Background()`, whose span is
the no-op one), nor kube-apiserver's or etcd's providers.

## The fix

`trace.otelSpan`'s docstring narrowed (no Lean statement changes; the opaque's type is the same):
an SDK span's provider is built from otel's own components only:

- sampler: `AlwaysSample`, `NeverSample`, `TraceIDRatioBased`, or `ParentBased` over these, with any
  of its four options over these (the default `ParentBased(AlwaysSample)` and every
  `OTEL_TRACES_SAMPLER` value the SDK accepts are among them, `sampler_env.go`);
- ID generator: the default (no `WithIDGenerator`);
- span processors: otel's Batch and Simple ones, over exporters whose `ExportSpans` and `Shutdown`
  return (the Simple processor exports inside `End`);
- (minor (b)) observability metrics: if the tracer was made with `OTEL_GO_X_OBSERVABILITY` set, the
  global `MeterProvider` is otel's default (none set) or `metric/noop`'s, never another.

These read no context key but otel's `currentSpanKey`. The closure clause ("whose `TracerProvider()`
is one of otel's, whose `Tracer(...).Start` returns another such span") keeps its meaning: a span of
such a provider has that provider, which makes such spans.

Chosen over a provider-configuration opaque (a second trusted predicate on providers, which
`otelSpan` would then refer to): the same restriction stated in one place, with no new opaque and no
change to any Lean statement.

Minor (b) needs the clause: a user `MeterProvider` installed with `otel.SetMeterProvider` receives the
span's context in `Enabled`/`Add` under the observability metrics (`TestOtelExcludedComponents`'
last case reads its own key there). kube-apiserver sets it to `metric/noop` at init
(`k8s.io/apiserver/pkg/server/options/tracing.go`), etcd never sets it.

Also updated (trusted text, docstrings only): `grpcRunCtx` (`Proof/google_golang_org/grpc/InvGrpc.lean`:
otelgrpc's tracer is etcd's provider, of the narrowed set) and `tracing.Start.spec`'s header
(`Spec/k8s_io/component_base/tracing/Start.lean`: the new span stays in the set, only such
components run on `ctx`).

## The producers of `trace.otelSpan`

All are trusted texts or carry an existing value; each still gives it:

- **grpc's run context** (`grpcRunCtx`, otelgrpc's `TagRPC`): etcd's only `otelgrpc.WithTracerProvider`
  is `setupTracingExporter`'s provider (`server/embed/config_tracing.go` at 673da07c8f):
  `NewTracerProvider(WithBatcher(otlptracegrpc exporter), WithResource, WithSampler(ParentBased(
  NeverSample | TraceIDRatioBased)))`, default ID generator; `ServerConfig.TracerOptions` is set only
  from it (`embed/etcd.go:251`). Remote parents: `nonRecordingSpan`. In the set.
- **`traceutil.Tracer.Start`**: the tracer the package variable holds is the no-op one in the model
  (`Tracer_init`); it returns `ctx`'s span or a no-op span. Were `traceutil.Init` specified, its
  argument in etcd is the same provider as above. In the set.
- **k8s `tracing.Start`**: the new span is made by the parent span's provider (closure clause), or
  the no-op provider when the context holds none. In the set.
- **Context laws** (`libCtxOk_of_ctxValueNil`, `_background`, `_todo`, `_bgFrom`, `_of_valueWand`,
  `_of_nil`, `k8sCtxOk_*`, the chain forms in `LibKeysChain.lean`): `nil` at the key, or the parent's
  value carried. Unaffected.
- **kube-apiserver's own providers** (`component-base/tracing.NewProvider`: `ParentBased(NeverSample
  | TraceIDRatioBased)`, `NewBatchSpanProcessor(otlptracegrpc)`, default ID generator): in the set
  (not a producer of any statement here; the request contexts of the closed k8s theorems are
  `Background()`'s).

Consumers (`trace.SpanFromContext`, `HistogramVec.WithContext`, `Tracer.Start`'s premise,
`tracing.SpanFromContext`) use only the methods-return part, unchanged.

## The Go evidence

`examples/premisefix/k8sctx/otelprovider_test.go` (run: `cd examples/premisefix/k8sctx && GOWORK=off
go test -count=1 -run TestOtel -v .`; all pass at sdk/trace v1.47.0, Go's execution tracer off, whose
key `k8sCtxOk` constrains, `rtrace_test.go`):

- `TestOtelComponentsReadOnlySpanKey`: every provider of the set (11 samplers plus the default, 4
  processor configurations), started from a context recording every key asked of it (no span, an SDK
  parent, a remote span context, a no-op span; nested; ended), asks only otel's `currentSpanKey`;
  k8s's `tracing.Start` on it asks only that and utiltrace's key (its own read); the samplers'
  `ShouldSample` and the processors' `OnStart` called directly ask only otel's key, resp. none.
- `TestOtelObservabilityReadsOnlySpanKey`: the same with `OTEL_GO_X_OBSERVABILITY=true`, under the
  default global `MeterProvider` and under `metric/noop`'s.
- `TestOtelRealProviders`: component-base's `NewProvider` (rates 0, 1000, 10^6 per million) and etcd's
  configuration (replicated, an in-memory exporter in place of OTLP's) ask only otel's key.
- `TestOtelExcludedComponents` (controls): a user `Sampler`, `IDGenerator`, `SpanProcessor`, and a user
  `MeterProvider` under the observability metrics, each reach the context at a key of its own: what
  the narrowed text excludes, and what the review's tests used.

## Statements

No Lean statement changes (docstrings of an opaque, a trusted `def` and a spec file only); no closed
theorem gains a premise. The axioms and `sorry`s are unchanged (`etc/tcb-report.py --check`).
