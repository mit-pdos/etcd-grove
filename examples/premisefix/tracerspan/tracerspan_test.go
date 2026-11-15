// Package tracerspan checks traceutil.Tracer.Start's span premise (k8s 7f-4 Revision 2, from
// etcd-grove-81's re-review): etcd's tracer is noop.NewTracerProvider().Tracer(...) (fork
// pkg/traceutil/trace.go:32), whose Start calls SpanContext() and IsRecording() on ctx's span.
//
//   - TestStartRefutes: a span whose End/AddEvent/RecordError return (trace.isSpan, hence
//     trace.spanCtxOk, the premise of Revision 1 and none at all before) but whose SpanContext
//     panics makes Start panic, under a context whose Done() is nil (mvcc.doneNil) and under
//     trace.ContextWithSpan(context.Background(), ...) (isContext): the old axiom was refuted.
//   - TestStartOtelSpans: with nil or one of otel's own spans at the key (trace.spanValOk:
//     nil or trace.otelSpan), Start returns.
package tracerspan

import (
	"context"
	"testing"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/codes"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"go.opentelemetry.io/otel/trace"
	"go.opentelemetry.io/otel/trace/embedded"
	"go.opentelemetry.io/otel/trace/noop"
)

// badSpan: End, AddEvent, RecordError return (trace.isSpan holds); SpanContext panics.
type badSpan struct{ embedded.Span }

func (badSpan) End(...trace.SpanEndOption)              {}
func (badSpan) AddEvent(string, ...trace.EventOption)   {}
func (badSpan) RecordError(error, ...trace.EventOption) {}
func (badSpan) AddLink(trace.Link)                      {}
func (badSpan) IsRecording() bool                       { return false }
func (badSpan) SpanContext() trace.SpanContext          { panic("SpanContext") }
func (badSpan) SetStatus(codes.Code, string)            {}
func (badSpan) SetName(string)                          {}
func (badSpan) SetAttributes(...attribute.KeyValue)     {}
func (badSpan) TracerProvider() trace.TracerProvider    { return nil }

// myCtx: Done() returns nil (mvcc.doneNil); Value returns badSpan at every key.
type myCtx struct{}

func (myCtx) Deadline() (time.Time, bool) { return time.Time{}, false }
func (myCtx) Done() <-chan struct{}       { return nil }
func (myCtx) Err() error                  { return nil }
func (myCtx) Value(any) any               { return badSpan{} }

func panics(f func()) (p bool) {
	defer func() { p = recover() != nil }()
	f()
	return false
}

func TestStartRefutes(t *testing.T) {
	tr := noop.NewTracerProvider().Tracer("go.etcd.io/etcd")
	if !panics(func() { tr.Start(myCtx{}, "x") }) {
		t.Error("doneNil context with a bad span: no panic")
	}
	if !panics(func() { tr.Start(trace.ContextWithSpan(context.Background(), badSpan{}), "x") }) {
		t.Error("ContextWithSpan(Background, bad span): no panic")
	}
}

func TestStartOtelSpans(t *testing.T) {
	tr := noop.NewTracerProvider().Tracer("go.etcd.io/etcd")
	_, sdkSpan := sdktrace.NewTracerProvider().Tracer("t").Start(context.Background(), "s")
	_, noopSpan := tr.Start(context.Background(), "s")
	remote := trace.ContextWithRemoteSpanContext(context.Background(), trace.SpanContext{})
	for i, ctx := range []context.Context{
		context.Background(),
		trace.ContextWithSpan(context.Background(), sdkSpan),
		trace.ContextWithSpan(context.Background(), noopSpan),
		remote,
	} {
		if panics(func() { tr.Start(ctx, "x") }) {
			t.Errorf("otel span %d: panic", i)
		}
	}
}
