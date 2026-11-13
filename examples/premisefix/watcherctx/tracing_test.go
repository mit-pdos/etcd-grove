package watcherctx

// T5-b's consequence for tracing.Start.wp_proof's post (Spec/k8s_io/component_base/tracing/Start.lean):
// the context Start returns answers the APF initialization-signal key as its parent does, with an
// otel SDK span in the parent and Go's execution tracer on (runtime/trace's task added) or off.

import (
	"bytes"
	"context"
	rtrace "runtime/trace"
	"testing"

	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	utilflowcontrol "k8s.io/apiserver/pkg/util/flowcontrol"
	"k8s.io/component-base/tracing"
)

// apfKeyRec answers as its parent and records the APF key if it is asked.
type apfKeyRec struct {
	context.Context
	asked *bool
}

func (c apfKeyRec) Value(k any) any {
	if keyType(k) == apfKeyType {
		*c.asked = true
	}
	return c.Context.Value(k)
}

func TestTracingStartKeepsAPFKey(t *testing.T) {
	tp := sdktrace.NewTracerProvider(sdktrace.WithSampler(sdktrace.AlwaysSample()))
	defer tp.Shutdown(context.Background())
	base, sp := tp.Tracer("t").Start(context.Background(), "parent")
	defer sp.End()
	sig := utilflowcontrol.NewInitializationSignal()
	for _, parent0 := range []context.Context{base, utilflowcontrol.WithInitializationSignal(base, sig)} {
		for _, tracer := range []bool{false, true} {
			asked := false
			parent := apfKeyRec{parent0, &asked}
			var ctx context.Context
			if tracer {
				var buf bytes.Buffer
				if err := rtrace.Start(&buf); err != nil {
					t.Fatal(err)
				}
				ctx, _ = tracing.Start(parent, "op")
				rtrace.Stop()
			} else {
				ctx, _ = tracing.Start(parent, "op")
			}
			if asked {
				t.Fatalf("tracer=%v: Start read the APF key", tracer)
			}
			// The key's value through the returned context, read by WatchInitialized's own lookup
			// (a nil one calls nothing; APF's signal is signalled, Wait returns).
			utilflowcontrol.WatchInitialized(ctx)
			if !asked {
				t.Fatalf("tracer=%v: the returned context did not ask its parent at the APF key", tracer)
			}
		}
	}
	sig.Wait()
}
