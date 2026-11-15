package k8s7e2attack

// k8s 7e-2, blocker B2 (notes/k8s-7e-2-draft.md): the trusted tracing.Start.spec carries
// "Done() never closes" (ctxNeverDone) from the incoming context to the one tracing.Start returns.
// Checked at the pin's component-base: from context.Background() (OpenTelemetry's noop tracer, the
// apiserver's default), and with a real SDK tracer provider whose span is in the context (what the
// apiserver uses when tracing is configured), the returned context's Done() is nil.

import (
	"context"
	"testing"

	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/trace"
	"k8s.io/component-base/tracing"
)

func TestTracingStartDoneNil(t *testing.T) {
	ctx, sp := tracing.Start(context.Background(), "List(recursive=true) etcd3")
	defer sp.End(0)
	if ctx.Done() != nil {
		t.Fatalf("noop tracer: Done() = %v, want nil", ctx.Done())
	}
	// nested: a second Start on the returned context
	ctx2, sp2 := tracing.Start(ctx, "nested")
	defer sp2.End(0)
	if ctx2.Done() != nil {
		t.Fatalf("nested noop: Done() = %v, want nil", ctx2.Done())
	}
}

func TestTracingStartDoneNilSDK(t *testing.T) {
	tp := sdktrace.NewTracerProvider(sdktrace.WithSampler(sdktrace.AlwaysSample()))
	defer tp.Shutdown(context.Background())
	pctx, parent := tp.Tracer("test").Start(context.Background(), "parent")
	defer parent.End()
	if !trace.SpanFromContext(pctx).SpanContext().IsValid() {
		t.Fatalf("parent span not recording")
	}
	ctx, sp := tracing.Start(pctx, "List(recursive=true) etcd3")
	defer sp.End(0)
	if !trace.SpanFromContext(ctx).SpanContext().IsValid() {
		t.Fatalf("child span not from the SDK tracer")
	}
	if ctx.Done() != nil {
		t.Fatalf("SDK tracer: Done() = %v, want nil", ctx.Done())
	}
}
