// Package isctxerr checks errors.IsCtxErr's premise (premise fixes 6, part B, 2026-11-11):
// Spec/errors/IsCtxErr.lean said errors.Is(err, target), with target the value of
// context.Canceled or context.DeadlineExceeded, returns (true if err == target) for every typed
// error err (context.isTypedErr). It does not: an error type whose Is or Unwrap method panics
// makes errors.Is panic (TestTypedErrorMayPanic). The premise is now context.isCtxErr err: err is
// Canceled's or DeadlineExceeded's value, the errors a done standard context's Err returns, on
// which errors.Is returns err == target without panicking (TestCtxErrors). etcd's callers
// (EtcdServer.parseProposeCtxErr, EtcdServer.LeaseRenew, the second errors.Is of
// watchServer.Watch) pass a done context's Err(); watchServer.Watch's first errors.Is takes the
// gRPC stream's Recv error, which is no context error (TestGrpcStatusErrNotCtxErr), and its proof
// uses the proved errors.Is over that error's tree instead.
// Found by the axiom review notes/axiom-review/isctxerr.md.
package isctxerr

import (
	"context"
	"errors"
	"testing"
	"time"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

// badIs: a typed error (it implements error) whose Is method panics.
type badIs struct{}

func (badIs) Error() string     { return "badIs" }
func (badIs) Is(err error) bool { panic("Is") }

// badUnwrap: a typed error whose Unwrap method panics.
type badUnwrap struct{}

func (badUnwrap) Error() string { return "badUnwrap" }
func (badUnwrap) Unwrap() error { panic("Unwrap") }

func panics(f func()) (p bool) {
	defer func() {
		if recover() != nil {
			p = true
		}
	}()
	f()
	return false
}

// The old premise (a typed error) admitted these: errors.Is panics.
func TestTypedErrorMayPanic(t *testing.T) {
	if !panics(func() { _ = errors.Is(badIs{}, context.Canceled) }) {
		t.Fatal("expected errors.Is(badIs{}, context.Canceled) to panic")
	}
	if !panics(func() { _ = errors.Is(badUnwrap{}, context.DeadlineExceeded) }) {
		t.Fatal("expected errors.Is(badUnwrap{}, context.DeadlineExceeded) to panic")
	}
}

// ctxErrs: the errors of done standard contexts (canceled, timed out, and children of each),
// each Canceled's or DeadlineExceeded's value.
func ctxErrs(t *testing.T) []error {
	t.Helper()
	c1, cancel1 := context.WithCancel(context.Background())
	cancel1()
	c2, cancel2 := context.WithTimeout(context.Background(), time.Nanosecond)
	defer cancel2()
	<-c2.Done()
	c3, cancel3 := context.WithCancel(c1)
	defer cancel3()
	c4, cancel4 := context.WithTimeout(c2, time.Hour)
	defer cancel4()
	c5, cancel5 := context.WithDeadline(context.Background(), time.Now().Add(-time.Second))
	defer cancel5()
	errs := []error{context.Canceled, context.DeadlineExceeded}
	for _, c := range []context.Context{c1, c2, c3, c4, c5} {
		<-c.Done()
		e := c.Err()
		if e != context.Canceled && e != context.DeadlineExceeded {
			t.Fatalf("a done context's Err() is %#v, neither Canceled nor DeadlineExceeded", e)
		}
		errs = append(errs, e)
	}
	return errs
}

// The new premise (context.isCtxErr): errors.Is returns err == target and does not panic.
func TestCtxErrors(t *testing.T) {
	for _, err := range ctxErrs(t) {
		for _, target := range []error{context.Canceled, context.DeadlineExceeded} {
			var b bool
			if panics(func() { b = errors.Is(err, target) }) {
				t.Fatalf("errors.Is(%v, %v) panicked", err, target)
			}
			if b != (err == target) {
				t.Fatalf("errors.Is(%v, %v) = %v, want %v", err, target, b, err == target)
			}
		}
	}
}

// etcd's parseProposeCtxErr and LeaseRenew switch on errors.Is(err, context.DeadlineExceeded)
// and errors.Is(err, context.Canceled) for err := cctx.Err() of a done context: one of the two
// holds, so their default branch (returning err itself) is not reached.
func TestEtcdSwitchExhaustive(t *testing.T) {
	for _, err := range ctxErrs(t) {
		switch {
		case errors.Is(err, context.DeadlineExceeded):
		case errors.Is(err, context.Canceled):
		default:
			t.Fatalf("the default branch is reached for %v", err)
		}
	}
}

// watchServer.Watch's first errors.Is(err, context.Canceled) takes the gRPC stream's Recv error,
// a status error (it has an Is method), not a context error: isCtxErr does not hold there, and
// errors.Is is still well-defined (false) on it.
func TestGrpcStatusErrNotCtxErr(t *testing.T) {
	err := status.Error(codes.Canceled, context.Canceled.Error())
	if err == context.Canceled || err == context.DeadlineExceeded {
		t.Fatal("a status error is a context error")
	}
	var b bool
	if panics(func() { b = errors.Is(err, context.Canceled) }) {
		t.Fatal("errors.Is of a status error panicked")
	}
	if b {
		t.Fatal("errors.Is(status.Error(codes.Canceled, ...), context.Canceled) = true")
	}
}
