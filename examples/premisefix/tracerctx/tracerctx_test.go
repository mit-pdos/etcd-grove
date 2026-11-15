// Package tracerctx checks premise fixes 8's addition to traceutil.Tracer.Start's trusted spec
// (decided by etcd-grove-81, 2026-11-11): the context Start returns keeps context.libCtxOk
// (Proof/context/LibKeys.lean), libCtxOk ctx -* libCtxOk ctx'. For every tracer etcd can install
// at the pin (the noop tracer, tracing off, and the otel SDK tracer as etcd's server builds it,
// as examples/sweeprepairs/tracer), Start's context answers Value at grpc's keys (mdIncomingKey,
// mdOutgoingKey, peerKey) as its argument does, and at otel's currentSpanKey either its argument's
// value or a span of one of otel's types.
package tracerctx

import (
	"context"
	"net"
	"reflect"
	"strconv"
	"strings"
	"testing"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	tracesdk "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/sdk/trace/tracetest"
	"go.opentelemetry.io/otel/trace"
	"go.opentelemetry.io/otel/trace/noop"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/peer"
)

// etcdSampler is etcd's determineSampler (server/embed/config_tracing.go).
func etcdSampler(samplingRate int) tracesdk.Sampler {
	if samplingRate == 0 {
		return tracesdk.NeverSample()
	}
	return tracesdk.TraceIDRatioBased(float64(samplingRate) / 1000000)
}

type tracerCase struct {
	name string
	tp   trace.TracerProvider
}

func tracers() []tracerCase {
	cs := []tracerCase{{"noop (tracing off)", noop.NewTracerProvider()}}
	for _, rate := range []int{0, 1, 500000, 1000000} {
		tp := tracesdk.NewTracerProvider(
			tracesdk.WithSyncer(tracetest.NewInMemoryExporter()),
			tracesdk.WithSampler(tracesdk.ParentBased(etcdSampler(rate))),
		)
		cs = append(cs, tracerCase{"sdk ParentBased rate " + strconv.Itoa(rate), tp})
	}
	return cs
}

// keyRecorder records the keys a library asks its Value for (the libraries' keys are unexported).
type keyRecorder struct {
	context.Context
	keys []any
}

func (r *keyRecorder) Value(k any) any { r.keys = append(r.keys, k); return r.Context.Value(k) }

func captureKey(t *testing.T, read func(context.Context)) any {
	r := &keyRecorder{Context: context.Background()}
	read(r)
	if len(r.keys) == 0 {
		t.Fatal("the library asked no key")
	}
	return r.keys[0]
}

// same: the identical value (a map, grpc's MD, by its identity).
func same(a, b any) bool {
	if a == nil || b == nil {
		return a == nil && b == nil
	}
	va, vb := reflect.ValueOf(a), reflect.ValueOf(b)
	if va.Type() != vb.Type() {
		return false
	}
	if va.Kind() == reflect.Map {
		return va.UnsafePointer() == vb.UnsafePointer()
	}
	if !va.Comparable() { // grpc's rawMD (a struct of slices)
		return reflect.DeepEqual(a, b)
	}
	return a == b
}

// otelType: v's dynamic type is declared in one of otel's packages.
func otelType(v any) bool {
	ty := reflect.TypeOf(v)
	for ty.Kind() == reflect.Pointer {
		ty = ty.Elem()
	}
	return strings.HasPrefix(ty.PkgPath(), "go.opentelemetry.io/otel")
}

func TestStartKeepsLibCtx(t *testing.T) {
	inKey := captureKey(t, func(c context.Context) { metadata.FromIncomingContext(c) })
	outKey := captureKey(t, func(c context.Context) { metadata.FromOutgoingContext(c) })
	peerKey := captureKey(t, func(c context.Context) { peer.FromContext(c) })
	spanKey := captureKey(t, func(c context.Context) { trace.SpanFromContext(c) })
	grpcKeys := map[string]any{"mdIncomingKey": inKey, "mdOutgoingKey": outKey, "peerKey": peerKey}

	runs := 0
	for _, tc := range tracers() {
		traceutil.Init(tc.tp)
		bg := context.Background()
		withMD := metadata.NewIncomingContext(bg, metadata.Pairs("token", "t"))
		withMD = metadata.NewOutgoingContext(withMD, metadata.Pairs("k", "v"))
		withMD = peer.NewContext(withMD, &peer.Peer{Addr: &net.TCPAddr{IP: net.IPv4(127, 0, 0, 1), Port: 1}})
		spanCtx, _ := traceutil.Tracer.Start(withMD, "parent")
		cctx, cancel := context.WithCancel(spanCtx)
		defer cancel()
		parents := map[string]context.Context{
			"Background":                 bg,
			"grpc values":                withMD,
			"grpc values, span context":  spanCtx,
			"WithCancel of span context": cctx,
			"StartTimeKey over span":     context.WithValue(spanCtx, traceutil.StartTimeKey{}, 1),
		}
		for pname, ctx := range parents {
			for i := 0; i < 20; i++ {
				ctx2, span := traceutil.Tracer.Start(ctx, "put")
				for kname, k := range grpcKeys {
					if got, want := ctx2.Value(k), ctx.Value(k); !same(got, want) {
						t.Fatalf("%s, parent %s: Value(%s) is %v, the argument's %v", tc.name, pname, kname, got, want)
					}
				}
				got, want := ctx2.Value(spanKey), ctx.Value(spanKey)
				if !same(got, want) {
					if got == nil || !otelType(got) {
						t.Fatalf("%s, parent %s: Value(currentSpanKey) is %T, neither the argument's nor otel's", tc.name, pname, got)
					}
					if _, ok := got.(trace.Span); !ok || !same(got, span) {
						t.Fatalf("%s, parent %s: Value(currentSpanKey) is not the span Start returned", tc.name, pname)
					}
				}
				span.End()
				runs++
			}
		}
	}
	t.Logf("%d Start calls over %d tracers: grpc's keys passed through, the span key the argument's or otel's span", runs, len(tracers()))
}
