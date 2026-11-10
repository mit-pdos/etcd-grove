// Package fmtarg checks which method fmt calls on an argument (premise fixes 4, fix 5, 2026-11-10),
// what fmt.argOk (Spec/fmt/Errorf.lean) assumes: for %v/%s fmt calls Format when the type has one
// (in place of Error or String), and Error in place of String when the type is an error; so a
// String method's spec says what fmt does only for a type with neither Format nor Error, and an
// Error method's only for a type without Format. A method fmt calls that panics with a value whose
// Error panics makes Sprintf panic (fmt re-raises a nested panic). Found by the round-2 premise
// attack (fmt-argOk-error-over-string-and-formatter).
package fmtarg

import (
	"context"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/url"
	"reflect"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

type boom struct{}

func (boom) Error() string { panic("nested") }

// String returns "s", Format panics: fmt calls Format.
type withFormat struct{}

func (withFormat) String() string             { return "s" }
func (withFormat) Format(f fmt.State, c rune) { panic(boom{}) }

// Error returns "e", Format panics: fmt calls Format.
type errWithFormat struct{}

func (errWithFormat) Error() string              { return "e" }
func (errWithFormat) Format(f fmt.State, c rune) { panic(boom{}) }

// String returns "s", Error panics: fmt calls Error.
type stringerAndError struct{}

func (stringerAndError) String() string { return "s" }
func (stringerAndError) Error() string  { panic(boom{}) }

// String alone, Error alone: called.
type stringer struct{}

func (stringer) String() string { return "s" }

type errOnly struct{}

func (errOnly) Error() string { return "e" }

func panics(f func()) (p bool) {
	defer func() { p = recover() != nil }()
	f()
	return
}

func TestMethodCalled(t *testing.T) {
	for _, verb := range []string{"%v", "%s"} {
		for _, c := range []struct {
			name  string
			arg   any
			panic bool
			out   string
		}{
			{"String with Format", withFormat{}, true, ""},
			{"Error with Format", errWithFormat{}, true, ""},
			{"String with Error", stringerAndError{}, true, ""},
			{"String alone", stringer{}, false, "s"},
			{"Error alone", errOnly{}, false, "e"},
		} {
			var out string
			p := panics(func() { out = fmt.Sprintf(verb, c.arg) })
			if p != c.panic || (!p && out != c.out) {
				t.Errorf("%s %s: panic %v, output %q; want panic %v, output %q", verb, c.name, p, out, c.panic, c.out)
			}
		}
	}
	// %w (Errorf): Error with Format calls Format too
	if !panics(func() { _ = fmt.Errorf("%w", errWithFormat{}) }) {
		t.Errorf("Errorf %%w of an error with Format: no panic")
	}
}

// TestNoFormatter: none of the error types the proofs' error predicates describe (http.errStrOk,
// cache's errStrOk, statusErrOk, isEtcdProgressNotifier's error clause; each assumes
// methodSet ei.ty !! "Format" = none) implements fmt.Formatter, so fmt calls their Error method:
// the standard library's errors the proofs see, grpc's *status.Error (from status.Error and from
// status.FromContextError(...).Err()), rpctypes' EtcdError (client side, from rpctypes.Error) and
// the context errors.
func TestNoFormatter(t *testing.T) {
	ft := reflect.TypeOf((*fmt.Formatter)(nil)).Elem()
	cctx, cancel := context.WithCancel(context.Background())
	cancel()
	dctx, dcancel := context.WithDeadline(context.Background(), time.Unix(0, 0))
	defer dcancel()
	errs := []error{io.EOF, io.ErrUnexpectedEOF, errors.New("x"), fmt.Errorf("%w", io.EOF),
		&url.Error{}, &net.OpError{}, http.ErrBodyReadAfterClose, http.ErrHandlerTimeout,
		context.Canceled, context.DeadlineExceeded, &net.DNSError{}, &net.AddrError{}, net.ErrClosed,
		status.Error(codes.Unavailable, "m"),
		status.FromContextError(cctx.Err()).Err(),
		status.FromContextError(dctx.Err()).Err(),
		rpctypes.Error(rpctypes.ErrGRPCNoLeader),
		rpctypes.Error(rpctypes.ErrGRPCCompacted),
		rpctypes.ErrNoLeader,
		dctx.Err(),
	}
	for _, e := range errs {
		if reflect.TypeOf(e).Implements(ft) {
			t.Errorf("%T implements fmt.Formatter", e)
		}
	}
	// the grpc and rpctypes errors are of the types the specs name
	if _, ok := status.Error(codes.Unavailable, "m").(interface{ GRPCStatus() *status.Status }); !ok {
		t.Errorf("status.Error: no GRPCStatus")
	}
	if _, ok := rpctypes.Error(rpctypes.ErrGRPCNoLeader).(rpctypes.EtcdError); !ok {
		t.Errorf("rpctypes.Error(ErrGRPCNoLeader) is %T, not rpctypes.EtcdError", rpctypes.Error(rpctypes.ErrGRPCNoLeader))
	}
	if !errors.Is(dctx.Err(), context.DeadlineExceeded) {
		t.Errorf("deadline context's Err is %v", dctx.Err())
	}
}
