package incomingoftest

import (
	"context"
	"errors"
	"testing"
)

// etcdError has rpctypes.EtcdError's shape (api/v3/v3rpc/rpctypes/error.go: a comparable struct of
// code and desc, value receiver Error, no Is method). errors.Is's behaviour depends only on that.
type etcdError struct {
	code int
	desc string
}

func (e etcdError) Error() string { return e.desc }

var errFutureRev = etcdError{11, "etcdserver: mvcc: required revision is a future revision"}

// descIs is a leaf error with an Is method that answers by description (what statusErrOk's
// grpcErrMethodsOk allows: Is returns true only for a target of the same description).
type descIs struct{ msg string }

func (e *descIs) Error() string        { return e.msg }
func (e *descIs) Is(target error) bool { return target.Error() == e.msg }

// B3 (Part B, IsStatusErr.spec): for an EtcdError target, errors.Is is true of an equal EtcdError,
// false of the context errors (no Is method, another dynamic type), and true of a leaf error of
// another type whose Is method says so: so "b = true -> err.ty = EtcdError.ty" holds only for
// errors without an Is method.
func TestIsEtcdTarget(t *testing.T) {
	cases := []struct {
		name string
		err  error
		want bool
	}{
		{"equal EtcdError", etcdError{11, errFutureRev.desc}, true},
		{"context.Canceled", context.Canceled, false},
		{"context.DeadlineExceeded", context.DeadlineExceeded, false},
		{"errors.New with the same text", errors.New(errFutureRev.desc), false},
		{"leaf error with an Is method, same text", &descIs{errFutureRev.desc}, true},
	}
	for _, c := range cases {
		got := errors.Is(c.err, errFutureRev)
		t.Logf("errors.Is(%T %q, EtcdError) = %v", c.err, c.err.Error(), got)
		if got != c.want {
			t.Fatalf("%s: got %v", c.name, got)
		}
	}
}

// B2 (Part B, ctxErrsErr's message form): the context errors' Error() is fixed and is no handler
// description.
func TestCtxErrMessages(t *testing.T) {
	handler := []string{"etcdserver: mvcc: required revision is a future revision",
		"etcdserver: mvcc: required revision has been compacted"}
	for _, e := range []error{context.Canceled, context.DeadlineExceeded} {
		m1, m2 := e.Error(), e.Error()
		t.Logf("%T: Error() = %q, %q", e, m1, m2)
		for _, h := range handler {
			if m1 != m2 || m1 == h {
				t.Fatal("unstable or a handler description")
			}
		}
	}
}
