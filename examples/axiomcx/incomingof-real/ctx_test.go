package incomingofreal

// incomingof Part B, option (a) (decided by etcd-grove-03, 2026-11-18): the narrowed T2 conjunct
// (ctxErrsErr/ctxErrClient: Err()'s non-nil error stably returns "context canceled" or "context
// deadline exceeded") and the strengthened rpctypes.Error / ContextError. Evidence at go1.27.3.

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
)

var errCause = errors.New("my custom cause: etcdserver: mvcc: required revision is a future revision")

// channelContext mirrors k8s.io/apimachinery/pkg/util/wait.ContextForChannel's type (wait.go):
// Done() is stopCh, Err() is context.Canceled once stopCh is closed.
type channelContext struct{ stopCh <-chan struct{} }

func (c channelContext) Done() <-chan struct{}       { return c.stopCh }
func (c channelContext) Deadline() (time.Time, bool) { return time.Time{}, false }
func (c channelContext) Value(key any) any           { return nil }
func (c channelContext) Err() error {
	select {
	case <-c.stopCh:
		return context.Canceled
	default:
		return nil
	}
}

type key struct{}

// doneContexts: every way of making a done context the producers of ctxErrsErr reach (Perennial's
// context model, context.ErrAny; k8s's channelContext, chanCtx_ok; value contexts, withVersion and
// tracing.Start), including the *Cause variants with a custom cause.
func doneContexts(t *testing.T) map[string]context.Context {
	m := map[string]context.Context{}
	c1, f1 := context.WithCancel(context.Background())
	f1()
	m["WithCancel"] = c1
	c2, f2 := context.WithCancelCause(context.Background())
	f2(errCause)
	m["WithCancelCause(custom)"] = c2
	c3, f3 := context.WithDeadline(context.Background(), time.Now().Add(-time.Second))
	defer f3()
	m["WithDeadline(past)"] = c3
	c4, f4 := context.WithDeadlineCause(context.Background(), time.Now().Add(-time.Second), errCause)
	defer f4()
	m["WithDeadlineCause(past, custom)"] = c4
	c5, f5 := context.WithTimeoutCause(context.Background(), time.Millisecond, errCause)
	defer f5()
	<-c5.Done()
	m["WithTimeoutCause(expired, custom)"] = c5
	c6, f6 := context.WithTimeout(context.Background(), time.Hour)
	f6()
	m["WithTimeout(canceled early)"] = c6
	c7, f7 := context.WithCancel(c2) // child of a parent canceled with a cause
	defer f7()
	m["WithCancel(child of cause-canceled)"] = c7
	c8, f8 := context.WithCancelCause(c4)
	defer f8(nil)
	m["WithCancelCause(child of deadline-cause)"] = c8
	m["WithValue(cause-canceled)"] = context.WithValue(c2, key{}, 1)
	ch := make(chan struct{})
	close(ch)
	m["channelContext(closed)"] = channelContext{ch}
	c9, f9 := context.WithCancel(channelContext{ch}) // propagateCancel's goroutine-free path
	defer f9()
	m["WithCancel(channelContext closed)"] = c9
	ch2 := make(chan struct{})
	c10, f10 := context.WithCancel(channelContext{ch2}) // propagateCancel's goroutine path
	defer f10()
	close(ch2)
	<-c10.Done()
	m["WithCancel(channelContext closed later)"] = c10
	c11, f11 := context.WithCancelCause(context.Background())
	stop := context.AfterFunc(c11, func() {})
	defer stop()
	f11(errCause)
	m["WithCancelCause+AfterFunc"] = c11
	return m
}

// TestCtxErrOnlyTwo: a done context's Err() is non-nil, one of Go's two errors, with one of the two
// messages, stable across calls; the custom cause shows only in context.Cause.
func TestCtxErrOnlyTwo(t *testing.T) {
	for name, ctx := range doneContexts(t) {
		<-ctx.Done()
		err := ctx.Err()
		if err == nil {
			t.Fatalf("%s: Err() = nil on a done context", name)
		}
		if err != context.Canceled && err != context.DeadlineExceeded {
			t.Fatalf("%s: Err() = %T %q, neither Canceled nor DeadlineExceeded", name, err, err)
		}
		m := err.Error()
		if m != "context canceled" && m != "context deadline exceeded" {
			t.Fatalf("%s: Err().Error() = %q", name, m)
		}
		if err.Error() != m || ctx.Err().Error() != m {
			t.Fatalf("%s: message not stable", name)
		}
		t.Logf("%s: Err() = %T %q; Cause = %v", name, err, m, context.Cause(ctx))
	}
	if context.WithoutCancel(context.Background()).Err() != nil {
		t.Fatal("WithoutCancel: Err() not nil")
	}
}

// TestRpctypesErrorUnchanged: rpctypes.Error returns an error with no GRPCStatus method whose
// Error() is not a key of errStringToError unchanged (the strengthened rpctypes.Error.spec), in
// particular the two context errors; a message that is a key is mapped (the guard is needed).
func TestRpctypesErrorUnchanged(t *testing.T) {
	for _, e := range []error{context.Canceled, context.DeadlineExceeded, errors.New("some other message")} {
		if got := rpctypes.Error(e); got != e {
			t.Fatalf("rpctypes.Error(%T %q) = %T %q, not unchanged", e, e, got, got)
		}
		t.Logf("rpctypes.Error(%T %q) unchanged", e, e)
	}
	k := errors.New(rpctypes.ErrFutureRev.Error())
	if got := rpctypes.Error(k); got == k {
		t.Fatalf("rpctypes.Error(%q) unchanged: it is a key", k)
	} else {
		t.Logf("rpctypes.Error(*errorString %q) = %T (a key: mapped)", k, got)
	}
}

// TestContextErrorTwice: ContextError (client.go) applied twice, as kv.Do then kv.Get do, to a
// context error on a done context returns the same context error: a context error comes back as one.
func TestContextErrorTwice(t *testing.T) {
	for name, ctx := range doneContexts(t) {
		<-ctx.Done()
		e := ctx.Err()
		once := clientv3.ContextError(ctx, e)
		twice := clientv3.ContextError(ctx, once)
		if once != e || twice != e {
			t.Fatalf("%s: ContextError(%q) = %T %q, then %T %q", name, e, once, once, twice, twice)
		}
	}
	// On a live context too (ContextError's rpctypes.Error branch only).
	for _, e := range []error{context.Canceled, context.DeadlineExceeded} {
		if got := clientv3.ContextError(context.Background(), clientv3.ContextError(context.Background(), e)); got != e {
			t.Fatalf("live ctx: ContextError twice of %q = %T %q", e, got, got)
		}
	}
	t.Log("ContextError twice returns the context error unchanged on every done context and on a live one")
}
