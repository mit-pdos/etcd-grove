// Package k8sctx checks the premises of premise fixes 7 (2026-11-11, part A) on the k8s side:
// audit.GetAuditIDTruncated reads ctx.Value(auditKey); component-base's tracing.SpanFromContext
// and tracing.Start read otel's current span (and call its methods) and utiltrace's trace;
// HistogramVec.WithContext(ctx)'s Observe reads otel's span and calls its SpanContext(). Their old
// premises (none, or ctxOk ∗ ctxErrClient) admit a nil context or one whose Value or span panics
// (TestBadContextPanics). The new premise (k8sctx.k8sCtxOk, Proof/k8s_io/apiserver/pkg/audit/
// CtxKeys.lean, and its parts) holds of the contexts k8s's storage code runs on: Background, TODO,
// wait.ContextForChannel, WithValue chains, and an apiserver request's context with an audit
// context, a utiltrace trace and an otel span (TestRealContexts).
package k8sctx

import (
	"context"
	"testing"
	"time"

	"go.opentelemetry.io/otel/trace"
	"go.opentelemetry.io/otel/trace/noop"
	"k8s.io/apimachinery/pkg/util/wait"
	"k8s.io/apiserver/pkg/audit"
	"k8s.io/component-base/metrics"
	"k8s.io/component-base/tracing"
	utiltrace "k8s.io/utils/trace"
)

type panicCtx struct{ context.Context }

func (panicCtx) Value(any) any { panic("Value") }

// badSpan: an otel span (it embeds noop.Span for the interface's private method) whose
// SpanContext and TracerProvider panic.
type badSpan struct{ noop.Span }

func (badSpan) SpanContext() trace.SpanContext       { panic("SpanContext") }
func (badSpan) TracerProvider() trace.TracerProvider { panic("TracerProvider") }

func panics(f func()) (p bool) {
	defer func() {
		if recover() != nil {
			p = true
		}
	}()
	f()
	return false
}

func newHist(t *testing.T) *metrics.HistogramVec {
	h := metrics.NewHistogramVec(&metrics.HistogramOpts{Name: "pf7_hist", Help: "h"}, []string{"l"})
	metrics.NewKubeRegistry().MustRegister(h)
	return h
}

func TestBadContextPanics(t *testing.T) {
	h := newHist(t)
	bad := map[string]context.Context{
		"nil":      nil,
		"panicCtx": panicCtx{context.Background()},
	}
	for name, ctx := range bad {
		for fname, f := range map[string]func(){
			"audit.GetAuditIDTruncated": func() { audit.GetAuditIDTruncated(ctx) },
			"tracing.SpanFromContext":   func() { tracing.SpanFromContext(ctx) },
			"tracing.Start":             func() { tracing.Start(ctx, "op") },
			"HistogramVec Observe":      func() { h.WithContext(ctx).WithLabelValues("x").Observe(1) },
		} {
			if name == "nil" && fname == "HistogramVec Observe" {
				continue // otel's SpanFromContext returns its no-op span on a nil context
			}
			if !panics(f) {
				t.Errorf("%s(%s): expected a panic", fname, name)
			}
		}
	}
	// A span whose methods panic, under otel's own key (trace.ContextWithSpan is exported).
	ctx := trace.ContextWithSpan(context.Background(), badSpan{})
	if !panics(func() { tracing.Start(ctx, "op") }) {
		t.Error("tracing.Start: expected a panic (TracerProvider)")
	}
	if !panics(func() { h.WithContext(ctx).WithLabelValues("x").Observe(1) }) {
		t.Error("HistogramVec Observe: expected a panic (SpanContext)")
	}
}

type otherKey struct{}

func TestRealContexts(t *testing.T) {
	h := newHist(t)
	stop := make(chan struct{})
	defer close(stop)
	bg := context.Background()
	c1, cancel := context.WithTimeout(context.WithValue(bg, otherKey{}, 1), time.Minute)
	defer cancel()
	// An apiserver request's context: an audit context, a utiltrace trace, an otel span.
	req := audit.WithAuditContext(bg)
	audit.WithAuditID(req, "0123456789012345678901234567890123456789012345678901234567890123456789")
	req = utiltrace.ContextWithTrace(req, utiltrace.New("req"))
	req, _ = noop.NewTracerProvider().Tracer("t").Start(req, "span")
	for name, ctx := range map[string]context.Context{
		"Background": bg, "TODO": context.TODO(), "ContextForChannel": wait.ContextForChannel(stop),
		"WithTimeout(WithValue)": c1, "request": req,
	} {
		_ = audit.GetAuditIDTruncated(ctx)
		sp := tracing.SpanFromContext(ctx)
		sp.AddEvent("e")
		c2, sp2 := tracing.Start(ctx, "op")
		sp2.AddEvent("e")
		_ = audit.GetAuditIDTruncated(c2)
		c3, sp3 := tracing.Start(c2, "nested")
		sp3.End(time.Hour)
		sp2.End(time.Hour)
		h.WithContext(ctx).WithLabelValues("x").Observe(1)
		h.WithContext(c3).WithLabelValues("x").Observe(1)
		t.Logf("%s: ok", name)
	}
	if got := audit.GetAuditIDTruncated(req); len(got) != 64 {
		t.Errorf("request: audit ID %q", got)
	}
}
