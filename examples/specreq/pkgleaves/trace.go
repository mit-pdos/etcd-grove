// Requirement snippets for pkg/v3/traceutil, request traces (batch 4b).
package pkgleaves

import (
	"context"
	"time"

	"go.opentelemetry.io/otel/attribute"
	"go.opentelemetry.io/otel/trace"
	"go.uber.org/zap"

	"go.etcd.io/etcd/pkg/v3/traceutil"
)

// REQ traceutil/request-trace: a request's trace is made once, found again down the call chain
// (the same trace), stepped, given fields, and logged; a span is started and ended around it.
// Users: server/etcdserver/v3_server.go:108-140 (Range: Tracer.Start, EnsureTrace, AddField,
// LogIfLong, Step), :1036-1048 (doSerialize: Get, Step), txn/range.go:48-81 (EnsureTrace on the
// request's context: the same trace), txn/put.go:106 (StepWithFunction), v3_server.go:1015
// (SpanFromContext(ctx).RecordError).
// Assumes: ctx is a context carrying no trace (grpc's per-call context); lg is zap's or nil;
// distributed tracing is not configured (traceutil.Init is never called).
// Specs: TraceUtil.Tracer.Start.spec (tracer_init), EnsureTrace.spec, Get.spec, Trace.Step.spec,
// Trace.StepWithFunction.spec, Trace.AddField.spec, Trace.LogIfLong.spec;
// OtelTrace.SpanFromContext.spec, WithAttributes.spec, OtelAttribute.String.spec; laws:
// ctxTraceIs_value (otel's key is not TraceKey), traceEmpty_agree.
func ReqRequestTrace(ctx context.Context, lg *zap.Logger, key string) {
	ctx, span := traceutil.Tracer.Start(ctx, "range", trace.WithAttributes(
		attribute.String("range_begin", key),
	))
	defer span.End()

	ctx, tr := traceutil.EnsureTrace(ctx, lg, "range",
		traceutil.Field{Key: "range_begin", Value: key},
	)
	defer tr.LogIfLong(100 * time.Millisecond)

	// further down the same chain (txn.Range): the request's trace, not a new one
	ctx2, tr2 := traceutil.EnsureTrace(ctx, lg, "range")
	if tr2 != tr || ctx2 != ctx {
		panic("request-trace: a second trace for one request")
	}
	if traceutil.Get(ctx) != tr {
		panic("request-trace: Get lost the request's trace")
	}
	tr.Step("agreement among raft nodes before linearized reading")
	tr.StepWithFunction(func() { tr.Step("inside: disabled") }, "get previous kv pair")
	tr.AddField(traceutil.Field{Key: "response_count", Value: 1})
	trace.SpanFromContext(ctx).RecordError(nil)
}

// REQ traceutil/apply-trace-handoff: a trace made on the apply thread (at context.TODO()) is
// handed with the apply result to the request goroutine, which re-times it and logs it.
// Users: txn/put.go:31 (EnsureTrace(context.TODO()...) via the applier), v3_server.go:1022-1029
// (raftRequest), :397-404 (Compact).
// Assumes: the trace travels by a channel (the wait registry): one owner at a time.
// Specs: EnsureTrace.spec (ctxTraceIs_todo), Trace.GetStartTime.spec, Trace.SetStartTime.spec,
// Trace.InsertStep.spec, Trace.LogIfLong.spec.
func ReqApplyTraceHandoff(lg *zap.Logger) {
	ch := make(chan *traceutil.Trace, 1)
	go func() {
		_, tr := traceutil.EnsureTrace(context.TODO(), lg, "put")
		tr.Step("apply")
		ch <- tr
	}()
	tr := <-ch
	start := time.Now()
	applyStart := tr.GetStartTime()
	tr.SetStartTime(start)
	tr.InsertStep(0, applyStart, "process raft request")
	tr.LogIfLong(100 * time.Millisecond)
}

// REQ traceutil/mvcc-todo-trace: mvcc's views begin a transaction with a fresh empty trace, which
// the transaction steps; it is never logged.
// Users: storage/mvcc/kv_view.go:31,40,47 (TODO()), kvstore_txn.go:108 (Step), kvstore.go:117.
// Assumes: nothing.
// Specs: TODO.spec, Trace.Step.spec, Trace.IsEmpty.spec.
func ReqMvccTodoTrace() {
	tr := traceutil.TODO()
	tr.Step("range keys from in-memory index tree")
	if !tr.IsEmpty() {
		panic("mvcc-todo-trace: TODO's trace not empty")
	}
}

// REQ traceutil/read-loop-trace: the read-index loop makes a trace per iteration at Background()
// and logs all its steps if long.
// Users: server/etcdserver/read/read.go:109-144.
// Assumes: lg is zap's or nil.
// Specs: EnsureTrace.spec (ctxTraceIs_background), Trace.Step.spec, Trace.AddField.spec,
// Trace.LogAllStepsIfLong.spec.
func ReqReadLoopTrace(lg *zap.Logger, idx uint64) {
	_, tr := traceutil.EnsureTrace(context.Background(), lg, "linearizableReadLoop")
	tr.Step("read index received")
	tr.AddField(traceutil.Field{Key: "readStateIndex", Value: idx})
	tr.LogAllStepsIfLong(100 * time.Millisecond)
}

// REQ traceutil/sub-trace: a transaction's operations are grouped in sub-traces.
// Users: server/etcdserver/txn/txn.go:146-160 (executeTxn).
// Assumes: tr is the caller's trace.
// Specs: Trace.StartSubTrace.spec, Trace.StopSubTrace.spec, Trace.Step.spec.
func ReqSubTrace(tr *traceutil.Trace, key string) {
	tr.StartSubTrace(traceutil.Field{Key: "req_type", Value: "range"},
		traceutil.Field{Key: "range_begin", Value: key})
	tr.Step("range keys from bolt db")
	tr.StopSubTrace()
}
