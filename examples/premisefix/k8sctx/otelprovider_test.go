// The narrowing of trace.otelSpan (2026-11-13, notes/otelspan-narrow.md; the context sweep's
// minor (a) and (b), notes/ctx-sweep-fixes.md). otel's SDK passes the caller's context to the
// provider's configured Sampler (ShouldSample's ParentContext), IDGenerator (NewIDs, NewSpanID) and
// every SpanProcessor.OnStart (sdk/trace v1.47.0 tracer.go, Start and newSpan), and, with
// OTEL_GO_X_OBSERVABILITY set, to the instruments of the global MeterProvider (observ.Tracer's
// SpanStarted, SpanLive, SpanEnded). trace.otelSpan now admits only spans of providers built from
// otel's own components: the samplers AlwaysSample, NeverSample, TraceIDRatioBased and ParentBased
// over these (the env-configured and default samplers are among them), the default ID generator,
// the Batch and Simple span processors; with the observability metrics on, the global MeterProvider
// is otel's default (none set) or its no-op one.
//
//   - TestOtelComponentsReadOnlySpanKey: every provider built from these components, started from
//     a context that records every key asked of it (no span, an SDK parent of the same provider, a
//     remote span context, a no-op span; nested; the span ended), asks only otel's currentSpanKey;
//     so do the samplers and the processors' OnStart called directly.
//   - TestOtelObservabilityReadsOnlySpanKey: the same with OTEL_GO_X_OBSERVABILITY on, under the
//     default global MeterProvider and under metric/noop's (which k8s.io/apiserver's
//     server/options installs at init).
//   - TestOtelRealProviders: component-base's tracing.NewProvider (kube-apiserver's) and etcd's
//     configuration (server/embed/config_tracing.go at the pin, replicated: ParentBased over
//     NeverSample or TraceIDRatioBased, WithBatcher) ask only otel's key.
//   - TestOtelExcludedComponents (controls): a user Sampler, IDGenerator or SpanProcessor reading
//     a key of its own (the sweep's TestReviewSamplerReadsKey, TestReviewProcessorReadsKey), and a
//     user MeterProvider under the observability metrics, do reach the context at that key: what
//     the narrowed text excludes.
//
// The execution tracer is off here: with it on the SDK also reads runtime/trace's key, which
// k8sctx.k8sCtxOk constrains (rtrace_test.go).
package k8sctx

import (
	"context"
	"fmt"
	"sort"
	"sync"
	"testing"
	"time"

	"go.opentelemetry.io/otel"
	"go.opentelemetry.io/otel/metric"
	metricnoop "go.opentelemetry.io/otel/metric/noop"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/sdk/trace/tracetest"
	"go.opentelemetry.io/otel/trace"
	"go.opentelemetry.io/otel/trace/noop"
	"k8s.io/component-base/tracing"
	tracingapi "k8s.io/component-base/tracing/api/v1"
)

// otelKeyType is otel's currentSpanKey's type, as %T prints it.
const otelKeyType = "trace.traceContextKeyType"

// utiltraceKeyType is k8s.io/utils/trace's ContextTraceKey, which tracing.Start reads itself.
const utiltraceKeyType = "trace.ContextTraceKey"

// keyLog records the type of every key asked of a recCtx.
type keyLog struct {
	mu   sync.Mutex
	keys map[string]bool
}

func (l *keyLog) add(k any) {
	l.mu.Lock()
	defer l.mu.Unlock()
	if l.keys == nil {
		l.keys = map[string]bool{}
	}
	l.keys[fmt.Sprintf("%T", k)] = true
}

func (l *keyLog) list() []string {
	l.mu.Lock()
	defer l.mu.Unlock()
	var out []string
	for k := range l.keys {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

// onlyOtel fails unless every key asked is otel's.
func (l *keyLog) onlyOtel(t *testing.T, what string) {
	t.Helper()
	for _, k := range l.list() {
		if k != otelKeyType {
			t.Errorf("%s: asked key %s", what, k)
		}
	}
}

// recCtx answers as its parent and records every key asked of it.
type recCtx struct {
	context.Context
	log *keyLog
}

func (c recCtx) Value(k any) any {
	c.log.add(k)
	return c.Context.Value(k)
}

func inSetSamplers() map[string]sdktrace.Sampler {
	base := map[string]sdktrace.Sampler{
		"AlwaysSample": sdktrace.AlwaysSample(), "NeverSample": sdktrace.NeverSample(),
		"TraceIDRatioBased(0)":   sdktrace.TraceIDRatioBased(0),
		"TraceIDRatioBased(0.5)": sdktrace.TraceIDRatioBased(0.5),
		"TraceIDRatioBased(1)":   sdktrace.TraceIDRatioBased(1),
	}
	out := map[string]sdktrace.Sampler{}
	for n, s := range base {
		out[n] = s
		out["ParentBased("+n+")"] = sdktrace.ParentBased(s)
	}
	out["ParentBased(TraceIDRatioBased(0.5), all four options)"] = sdktrace.ParentBased(
		sdktrace.TraceIDRatioBased(0.5),
		sdktrace.WithRemoteParentSampled(sdktrace.NeverSample()),
		sdktrace.WithRemoteParentNotSampled(sdktrace.AlwaysSample()),
		sdktrace.WithLocalParentSampled(sdktrace.ParentBased(sdktrace.NeverSample())),
		sdktrace.WithLocalParentNotSampled(sdktrace.TraceIDRatioBased(0.5)))
	out["default (NewTracerProvider without WithSampler)"] = nil
	return out
}

func inSetProcessors() map[string]func() []sdktrace.TracerProviderOption {
	exp := func() *tracetest.InMemoryExporter { return tracetest.NewInMemoryExporter() }
	return map[string]func() []sdktrace.TracerProviderOption{
		"none": func() []sdktrace.TracerProviderOption { return nil },
		"WithBatcher": func() []sdktrace.TracerProviderOption {
			return []sdktrace.TracerProviderOption{sdktrace.WithBatcher(exp())}
		},
		"WithSyncer": func() []sdktrace.TracerProviderOption {
			return []sdktrace.TracerProviderOption{sdktrace.WithSyncer(exp())}
		},
		"Batch+Simple": func() []sdktrace.TracerProviderOption {
			return []sdktrace.TracerProviderOption{
				sdktrace.WithSpanProcessor(sdktrace.NewBatchSpanProcessor(exp())),
				sdktrace.WithSpanProcessor(sdktrace.NewSimpleSpanProcessor(exp())),
			}
		},
	}
}

// parents: the contexts a span is started from (each to be wrapped in a recCtx).
func parents(tp trace.TracerProvider) map[string]context.Context {
	bg := context.Background()
	sdkParent, _ := tp.Tracer("p").Start(bg, "parent")
	sc := trace.NewSpanContext(trace.SpanContextConfig{
		TraceID: trace.TraceID{1}, SpanID: trace.SpanID{2}, TraceFlags: trace.FlagsSampled, Remote: true})
	noopParent, _ := noop.NewTracerProvider().Tracer("n").Start(bg, "noop")
	return map[string]context.Context{
		"no span": bg, "SDK parent": sdkParent,
		"remote span context": trace.ContextWithRemoteSpanContext(bg, sc), "noop span": noopParent,
	}
}

// exercise starts a span from each parent through a recCtx, nests one, and ends both; through
// k8s's tracing.Start too (it starts on the context's span's TracerProvider).
func exercise(t *testing.T, tp trace.TracerProvider, what string) {
	t.Helper()
	for pn, p := range parents(tp) {
		log := &keyLog{}
		ctx := recCtx{p, log}
		c1, s1 := tp.Tracer("t").Start(ctx, "op", trace.WithAttributes())
		c2, s2 := tp.Tracer("t").Start(c1, "nested")
		_ = c2
		s2.End()
		s1.End()
		log.onlyOtel(t, what+", parent "+pn)
		// k8s's tracing.Start also reads utiltrace's key itself (k8sctx.k8sCtxOk's).
		klog := &keyLog{}
		kctx := recCtx{p, klog}
		c3, s3 := tracing.Start(kctx, "k8s")
		_, s4 := tracing.Start(c3, "k8s-nested")
		s4.End(time.Hour)
		s3.End(time.Hour)
		for _, k := range klog.list() {
			if k != otelKeyType && k != utiltraceKeyType {
				t.Errorf("%s, parent %s, tracing.Start: asked key %s", what, pn, k)
			}
		}
	}
}

func TestOtelComponentsReadOnlySpanKey(t *testing.T) {
	for sn, s := range inSetSamplers() {
		for pn, popts := range inSetProcessors() {
			opts := popts()
			if s != nil {
				opts = append(opts, sdktrace.WithSampler(s))
			}
			tp := sdktrace.NewTracerProvider(opts...)
			exercise(t, tp, sn+" / "+pn)
			_ = tp.Shutdown(context.Background())
		}
		if s == nil {
			continue
		}
		// The sampler on its own, from each parent.
		for pn, p := range parents(sdktrace.NewTracerProvider()) {
			log := &keyLog{}
			_ = s.ShouldSample(sdktrace.SamplingParameters{ParentContext: recCtx{p, log}, TraceID: trace.TraceID{3}, Name: "x"})
			log.onlyOtel(t, sn+".ShouldSample, parent "+pn)
		}
	}
	// The processors' OnStart on their own.
	tp := sdktrace.NewTracerProvider()
	_, sp := tp.Tracer("t").Start(context.Background(), "s")
	rw := sp.(sdktrace.ReadWriteSpan)
	for n, proc := range map[string]sdktrace.SpanProcessor{
		"Batch":  sdktrace.NewBatchSpanProcessor(tracetest.NewInMemoryExporter()),
		"Simple": sdktrace.NewSimpleSpanProcessor(tracetest.NewInMemoryExporter()),
	} {
		log := &keyLog{}
		proc.OnStart(recCtx{context.Background(), log}, rw)
		if ks := log.list(); len(ks) != 0 {
			t.Errorf("%s.OnStart asked %v", n, ks)
		}
		_ = proc.Shutdown(context.Background())
	}
}

func TestOtelObservabilityReadsOnlySpanKey(t *testing.T) {
	t.Setenv("OTEL_GO_X_OBSERVABILITY", "true")
	run := func(mp string) {
		for pn, popts := range inSetProcessors() {
			opts := append(popts(), sdktrace.WithSampler(sdktrace.ParentBased(sdktrace.AlwaysSample())))
			tp := sdktrace.NewTracerProvider(opts...)
			exercise(t, tp, "observability, "+mp+" / "+pn)
			_ = tp.Shutdown(context.Background())
		}
	}
	t.Logf("global MeterProvider before any set: %T", otel.GetMeterProvider())
	run("default global MeterProvider")
	otel.SetMeterProvider(metricnoop.NewMeterProvider())
	run("metric/noop MeterProvider")
}

func TestOtelRealProviders(t *testing.T) {
	for _, rate := range []int32{0, 1000, 1000000} {
		r := rate
		endpoint := "127.0.0.1:1"
		tp, err := tracing.NewProvider(context.Background(),
			&tracingapi.TracingConfiguration{Endpoint: &endpoint, SamplingRatePerMillion: &r}, nil, nil)
		if err != nil {
			t.Fatal(err)
		}
		exercise(t, tp, fmt.Sprintf("component-base NewProvider, rate %d", rate))
		// tp's exporter cannot connect: shut it down without waiting.
		sctx, cancel := context.WithTimeout(context.Background(), 10*time.Millisecond)
		_ = tp.Shutdown(sctx)
		cancel()
	}
	// etcd's configuration (server/embed/config_tracing.go at 673da07c8f), with an in-memory
	// exporter in place of otlptracegrpc's (the exporter never receives the caller's context).
	for _, rate := range []int{0, 1000, 1000000} {
		var root sdktrace.Sampler = sdktrace.NeverSample()
		if rate != 0 {
			root = sdktrace.TraceIDRatioBased(float64(rate) / 1000000)
		}
		tp := sdktrace.NewTracerProvider(
			sdktrace.WithBatcher(tracetest.NewInMemoryExporter()),
			sdktrace.WithSampler(sdktrace.ParentBased(root)))
		exercise(t, tp, fmt.Sprintf("etcd's provider, rate %d", rate))
		_ = tp.Shutdown(context.Background())
	}
}

// Controls: components outside the narrowed set reach the caller's context at a key of their own.

type ownKey struct{}

type readingSampler2 struct{ sdktrace.Sampler }

func (s readingSampler2) ShouldSample(p sdktrace.SamplingParameters) sdktrace.SamplingResult {
	_ = p.ParentContext.Value(ownKey{})
	return s.Sampler.ShouldSample(p)
}

type readingIDGen struct{}

func (readingIDGen) NewIDs(ctx context.Context) (trace.TraceID, trace.SpanID) {
	_ = ctx.Value(ownKey{})
	return trace.TraceID{4}, trace.SpanID{5}
}

func (readingIDGen) NewSpanID(ctx context.Context, _ trace.TraceID) trace.SpanID {
	_ = ctx.Value(ownKey{})
	return trace.SpanID{6}
}

type readingProc2 struct{}

func (readingProc2) OnStart(ctx context.Context, _ sdktrace.ReadWriteSpan) { _ = ctx.Value(ownKey{}) }
func (readingProc2) OnEnd(sdktrace.ReadOnlySpan)                           {}
func (readingProc2) Shutdown(context.Context) error                        { return nil }
func (readingProc2) ForceFlush(context.Context) error                      { return nil }

type readingMP struct{ metricnoop.MeterProvider }
type readingMeter struct{ metricnoop.Meter }
type readingCounter struct{ metricnoop.Int64Counter }
type readingUpDown struct{ metricnoop.Int64UpDownCounter }

func (readingMP) Meter(string, ...metric.MeterOption) metric.Meter { return readingMeter{} }
func (readingMeter) Int64Counter(string, ...metric.Int64CounterOption) (metric.Int64Counter, error) {
	return readingCounter{}, nil
}
func (readingMeter) Int64UpDownCounter(string, ...metric.Int64UpDownCounterOption) (metric.Int64UpDownCounter, error) {
	return readingUpDown{}, nil
}
func (readingCounter) Enabled(ctx context.Context) bool { _ = ctx.Value(ownKey{}); return true }
func (readingUpDown) Enabled(ctx context.Context) bool  { _ = ctx.Value(ownKey{}); return true }

func asksOwnKey(t *testing.T, tp trace.TracerProvider, what string) {
	t.Helper()
	log := &keyLog{}
	_, s := tp.Tracer("t").Start(recCtx{context.Background(), log}, "op")
	s.End()
	got := log.keys[fmt.Sprintf("%T", ownKey{})]
	t.Logf("%s: keys asked %v", what, log.list())
	if !got {
		t.Errorf("%s: expected the component to ask its own key", what)
	}
}

func TestOtelExcludedComponents(t *testing.T) {
	asksOwnKey(t, sdktrace.NewTracerProvider(sdktrace.WithSampler(readingSampler2{sdktrace.AlwaysSample()})), "user Sampler")
	asksOwnKey(t, sdktrace.NewTracerProvider(sdktrace.WithIDGenerator(readingIDGen{})), "user IDGenerator")
	asksOwnKey(t, sdktrace.NewTracerProvider(sdktrace.WithSpanProcessor(readingProc2{})), "user SpanProcessor")
	t.Setenv("OTEL_GO_X_OBSERVABILITY", "true")
	prev := otel.GetMeterProvider()
	otel.SetMeterProvider(readingMP{})
	defer otel.SetMeterProvider(prev)
	asksOwnKey(t, sdktrace.NewTracerProvider(), "user MeterProvider, observability on")
}
