// Package ctxdone checks the Done() half of grpc's ctxOk (premise fixes 5, 2026-11-10;
// Proof/google_golang_org/grpc/InvGrpc.lean, notes/axiom-review/ctxok-done.md).
//
// ctxOk's quiet case (ctxQuiet) says Done() returns the nil channel and Err() nil; its third case
// (ctxErrs) says Done() returns, without panicking, the nil channel or a channel whose closing
// means the context is done (then Err() is not nil). Until premise fixes 5 neither said anything
// of Done(), and the axioms taking ctxOk that select on ctx.Done() (waitRetryBackoff, grpc's
// Invoke and NewStream) covered the two contexts TestOutsideContractPanics builds, on which
// waitRetryBackoff panics.
//
// TestProducers checks the new clauses on the contexts the proofs produce them for:
// context.TODO() and context.Background() (ctxQuiet_todo, ctxQuiet_background), a value context
// over TODO (withVersion's), and k8s's wait.ContextForChannel (chanCtx_ok), open and closed.
// TestRetryBackoff runs waitRetryBackoff on them: it returns.
package ctxdone

import (
	"context"
	"errors"
	"testing"
	"time"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

// Copies of etcd's waitRetryBackoff and contextErrToGRPCErr (client/v3/retry_interceptor.go:317,
// :365, github.com/upamanyus/etcd/client/v3 a4d2bb1720b9, examples/go.mod's replacement): both
// are unexported.
type options struct{ backoffFunc func(uint) time.Duration }

func waitRetryBackoff(ctx context.Context, attempt uint, callOpts *options) error {
	waitTime := time.Duration(0)
	if attempt > 0 {
		waitTime = callOpts.backoffFunc(attempt)
	}
	if waitTime > 0 {
		timer := time.NewTimer(waitTime)
		select {
		case <-ctx.Done():
			timer.Stop()
			return contextErrToGRPCErr(ctx.Err())
		case <-timer.C:
		}
	}
	return nil
}

func contextErrToGRPCErr(err error) error {
	switch {
	case errors.Is(err, context.DeadlineExceeded):
		return status.Error(codes.DeadlineExceeded, err.Error())
	case errors.Is(err, context.Canceled):
		return status.Error(codes.Canceled, err.Error())
	default:
		return status.Error(codes.Unknown, err.Error())
	}
}

// A copy of k8s's channelContext (k8s.io/apimachinery/pkg/util/wait/wait.go:117-142, at
// 0b7d352f711c, examples/k8s/*/go.mod's): the examples module does not depend on apimachinery.
type channelContext struct{ stopCh <-chan struct{} }

func contextForChannel(parentCh <-chan struct{}) context.Context {
	return channelContext{stopCh: parentCh}
}

func (c channelContext) Done() <-chan struct{} { return c.stopCh }
func (c channelContext) Err() error {
	select {
	case <-c.stopCh:
		return context.Canceled
	default:
		return nil
	}
}
func (c channelContext) Deadline() (time.Time, bool) { return time.Time{}, false }
func (c channelContext) Value(key any) any           { return nil }

type key struct{}

// quiet: ctxQuiet's clauses (Done() is nil, Err() is nil).
func quiet(t *testing.T, name string, ctx context.Context) {
	if ctx.Done() != nil {
		t.Errorf("%s: Done() is not the nil channel", name)
	}
	if ctx.Err() != nil {
		t.Errorf("%s: Err() = %v, want nil", name, ctx.Err())
	}
}

// closed reports whether ch is closed (a receive proceeds); nil is never.
func closed(ch <-chan struct{}) bool {
	if ch == nil {
		return false
	}
	select {
	case <-ch:
		return true
	default:
		return false
	}
}

// doneOk: ctxDoneCh's clause: Done() returns; if it is closed, Err() is not nil.
func doneOk(t *testing.T, name string, ctx context.Context) {
	ch := ctx.Done()
	if closed(ch) && ctx.Err() == nil {
		t.Errorf("%s: Done() closed but Err() is nil", name)
	}
}

func TestProducers(t *testing.T) {
	quiet(t, "TODO", context.TODO())
	quiet(t, "Background", context.Background())
	quiet(t, "WithValue(TODO)", context.WithValue(context.TODO(), key{}, 1))

	stop := make(chan struct{})
	cc := contextForChannel(stop)
	doneOk(t, "ContextForChannel (open)", cc)
	if closed(cc.Done()) || cc.Err() != nil {
		t.Errorf("ContextForChannel (open): done or Err() = %v", cc.Err())
	}
	close(stop)
	doneOk(t, "ContextForChannel (closed)", cc)
	if !closed(cc.Done()) || !errors.Is(cc.Err(), context.Canceled) {
		t.Errorf("ContextForChannel (closed): not done or Err() = %v", cc.Err())
	}
	// a value context over it delegates Done and Err (withVersion's)
	doneOk(t, "WithValue(ContextForChannel)", context.WithValue(cc, key{}, 1))
}

var opts = &options{backoffFunc: func(uint) time.Duration { return 10 * time.Millisecond }}

func TestRetryBackoff(t *testing.T) {
	for _, c := range []struct {
		name string
		ctx  context.Context
	}{
		{"TODO", context.TODO()},
		{"Background", context.Background()},
		{"WithValue(TODO)", context.WithValue(context.TODO(), key{}, 1)},
		{"ContextForChannel (open)", contextForChannel(make(chan struct{}))},
	} {
		if err := waitRetryBackoff(c.ctx, 1, opts); err != nil {
			t.Errorf("%s: waitRetryBackoff = %v, want nil", c.name, err)
		}
	}
	stop := make(chan struct{})
	close(stop)
	err := waitRetryBackoff(contextForChannel(stop), 1, opts)
	if status.Code(err) != codes.Canceled {
		t.Errorf("ContextForChannel (closed): waitRetryBackoff = %v, want a Canceled status", err)
	}
}

// quietDone: Err() is always nil (the old ctxQuiet held), Done() a closed channel.
type quietDone struct{ context.Context }

func (quietDone) Err() error { return nil }

// quietPanic: Err() is always nil (the old ctxQuiet held), Done() panics on its nil receiver.
type quietPanic struct{ ch chan struct{} }

func (*quietPanic) Deadline() (time.Time, bool) { return time.Time{}, false }
func (q *quietPanic) Done() <-chan struct{}     { return q.ch }
func (*quietPanic) Err() error                  { return nil }
func (*quietPanic) Value(any) any               { return nil }

func panics(f func()) (r any) {
	defer func() { r = recover() }()
	f()
	return nil
}

func TestOutsideContractPanics(t *testing.T) {
	c, cancel := context.WithCancel(context.Background())
	cancel()
	if panics(func() { waitRetryBackoff(quietDone{c}, 1, opts) }) == nil {
		t.Errorf("Done() closed, Err() nil: waitRetryBackoff did not panic (contextErrToGRPCErr(nil))")
	}
	var q *quietPanic
	if panics(func() { waitRetryBackoff(q, 1, opts) }) == nil {
		t.Errorf("Done() panicking: waitRetryBackoff did not panic")
	}
	// neither meets the new clauses
	if panics(func() { quietDone{c}.Done() }) != nil || !closed(quietDone{c}.Done()) {
		t.Errorf("quietDone: Done() should return a closed channel")
	}
}
