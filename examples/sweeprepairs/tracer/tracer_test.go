// Package tracer attacks the sweep-repairs-1 B2 addition to traceutil.Tracer.Start's trusted
// spec: the context Start returns answers Value(traceutil.StartTimeKey{}) as its argument does
// (startTimeOk ctx -* startTimeOk ctx'), for every tracer etcd can install at the pin: the noop
// tracer (tracing off, traceutil's default) and the otel SDK tracer as etcd's server builds it
// (server/embed/config_tracing.go: ParentBased(NeverSample or TraceIDRatioBased(rate/1e6))).
package tracer

import (
	"context"
	"testing"
	"time"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	tracesdk "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/sdk/trace/tracetest"
	"go.opentelemetry.io/otel/trace"
	"go.opentelemetry.io/otel/trace/noop"
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
		cs = append(cs, tracerCase{"sdk ParentBased rate " + itoa(rate), tp})
	}
	return cs
}

func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	s := ""
	for n > 0 {
		s = string(rune('0'+n%10)) + s
		n /= 10
	}
	return s
}

func TestStartKeepsStartTime(t *testing.T) {
	now := time.Now()
	runs := 0
	for _, tc := range tracers() {
		traceutil.Init(tc.tp)
		// the parent contexts: absent, a time.Time, and each of those under a span context
		spanAbsent, _ := traceutil.Tracer.Start(context.Background(), "parent")
		spanTime, _ := traceutil.Tracer.Start(
			context.WithValue(context.Background(), traceutil.StartTimeKey{}, now), "parent")
		timeOverSpan := context.WithValue(spanAbsent, traceutil.StartTimeKey{}, now)
		parents := map[string]context.Context{
			"absent":                     context.Background(),
			"time.Time":                  context.WithValue(context.Background(), traceutil.StartTimeKey{}, now),
			"span context, absent":       spanAbsent,
			"span context, time.Time":    spanTime,
			"time.Time over span context": timeOverSpan,
		}
		for pname, ctx := range parents {
			for i := 0; i < 50; i++ {
				ctx2, span := traceutil.Tracer.Start(ctx, "delete_range")
				want := ctx.Value(traceutil.StartTimeKey{})
				got := ctx2.Value(traceutil.StartTimeKey{})
				if got != want {
					t.Fatalf("%s, parent %s: Start's context answers %v, its argument %v", tc.name, pname, got, want)
				}
				if want != nil {
					if _, ok := got.(time.Time); !ok {
						t.Fatalf("%s, parent %s: %v is not a time.Time", tc.name, pname, got)
					}
				}
				span.End()
				runs++
			}
		}
	}
	t.Logf("%d Start calls over %d tracers, every answer the argument's", runs, len(tracers()))
}
