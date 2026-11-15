// The context sweep's fixes (2026-11-13, notes/ctx-sweep-fixes.md): tracing.Start with an otel SDK
// recording span in the context and Go's execution tracer on. The SDK's tracer.Start calls
// runtime/trace.NewTask(ctx, ...) (sdk/trace v1.47.0 span.go:844-849, recordingSpan.runtimeTrace),
// which reads ctx.Value(traceContextKey{}) and the *Task's id (go1.27.3 runtime/trace
// annotation.go:39, 65), a key k8sctx.k8sCtxOk did not constrain.
//
//   - TestStartRuntimeTraceKeyPanics: a context answering its parent everywhere but at runtime/trace's
//     key, where its Value panics, met tracing.Start.spec's old premise; tracing.Start returns with
//     the execution tracer off and panics with it on (kube-apiserver turns it on in-process through
//     /debug/pprof/trace). Also with a typed-nil *Task there (fromContext(ctx).id dereferences it).
//   - TestStartRuntimeTraceTask: the new fact (rtrace.taskRes: not a *Task, or a non-nil one) holds of
//     the context tracing.Start returns, with the tracer on (a fresh *Task) and off (the parent's
//     answer), and of the parent (nil).
package k8sctx

import (
	"bytes"
	"context"
	"fmt"
	"reflect"
	rtrace "runtime/trace"
	"testing"

	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"k8s.io/component-base/tracing"
)

func isRtraceKey(k any) bool { return fmt.Sprintf("%T", k) == "trace.traceContextKey" }

// rtKeyCtx: answers its parent everywhere but at runtime/trace's key, where it panics (or, with
// typedNil, answers a typed-nil *trace.Task). Done()/Err()/Deadline() are its parent's (ctxQuiet
// over Background); the audit, utiltrace, grpc metadata and peer keys answer nil, otel's
// currentSpanKey the SDK's span (trace.otelSpan).
type rtKeyCtx struct {
	context.Context
	typedNil bool
}

func (c rtKeyCtx) Value(k any) any {
	if isRtraceKey(k) {
		if c.typedNil {
			return (*rtrace.Task)(nil)
		}
		panic("Value at runtime/trace's key")
	}
	return c.Context.Value(k)
}

// keyRec records runtime/trace's key when it is asked (its type is unexported).
type keyRec struct {
	context.Context
	key *any
}

func (c keyRec) Value(k any) any {
	if isRtraceKey(k) {
		*c.key = k
	}
	return c.Context.Value(k)
}

func panicValue(f func()) (p any) {
	defer func() { p = recover() }()
	f()
	return nil
}

func sdkSpanCtx(t *testing.T) context.Context {
	tp := sdktrace.NewTracerProvider(sdktrace.WithSampler(sdktrace.AlwaysSample()))
	t.Cleanup(func() { tp.Shutdown(context.Background()) })
	base, parent := tp.Tracer("t").Start(context.Background(), "parent")
	t.Cleanup(func() { parent.End() })
	return base
}

func withExecTracer(t *testing.T, f func()) {
	var buf bytes.Buffer
	if err := rtrace.Start(&buf); err != nil {
		t.Fatal(err)
	}
	defer rtrace.Stop()
	f()
}

func TestStartRuntimeTraceKeyPanics(t *testing.T) {
	for _, typedNil := range []bool{false, true} {
		ctx := rtKeyCtx{sdkSpanCtx(t), typedNil}
		if p := panicValue(func() { tracing.Start(ctx, "op") }); p != nil {
			t.Fatalf("typedNil=%v: unexpected panic without the execution tracer: %v", typedNil, p)
		}
		var p any
		withExecTracer(t, func() { p = panicValue(func() { tracing.Start(ctx, "op") }) })
		if p == nil {
			t.Fatalf("typedNil=%v: expected tracing.Start to panic", typedNil)
		}
		t.Logf("typedNil=%v: tracing.Start panicked: %v", typedNil, p)
	}
}

func TestStartRuntimeTraceTask(t *testing.T) {
	var key any
	parent := keyRec{sdkSpanCtx(t), &key}
	var ctx1 context.Context
	withExecTracer(t, func() { ctx1, _ = tracing.Start(parent, "op") })
	if key == nil {
		t.Fatal("runtime/trace's key was not read")
	}
	if v := parent.Value(key); v != nil {
		t.Fatalf("parent: %v", v)
	}
	taskTy := reflect.TypeOf((*rtrace.Task)(nil))
	v1 := ctx1.Value(key)
	if reflect.TypeOf(v1) != taskTy || reflect.ValueOf(v1).IsNil() {
		t.Fatalf("tracer on: Value(traceContextKey{}) = %#v, want a non-nil *trace.Task", v1)
	}
	ctx0, _ := tracing.Start(parent, "op")
	if v0 := ctx0.Value(key); v0 != nil {
		t.Fatalf("tracer off: Value(traceContextKey{}) = %#v, want the parent's nil", v0)
	}
	// A child of the tracer-on context, started with the tracer on: NewTask reads its task.
	withExecTracer(t, func() {
		if p := panicValue(func() { tracing.Start(ctx1, "child") }); p != nil {
			t.Fatalf("child: %v", p)
		}
	})
}
