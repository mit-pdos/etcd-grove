package watcherctx

// k8s 7f-5a-P step 5 (notes/k8s-7f5a-draft.md §11): the Go evidence for the trusted text
// errors.AsLeafTy (Spec/errors/AsLeafTy.lean): errors.As(err, &target) returns false, the target
// unchanged, for a leaf error (no As, no Unwrap method) whose dynamic type is outside the target's
// type set. The watcher's interpretWatchError (watcher.go, errors.go:37) calls
// errors.As(err, &corruptobjDeletedErr) with a *corruptObjectDeletedError target on every error the
// producers send: a *status.Error (grpc; rpctypes' ErrGRPC* values are *status.Error at runtime),
// an rpctypes.EtcdError (from rpctypes.Error(..)), context.DeadlineExceeded, a *StatusError
// (apimachinery), and an *errors.errorString (errors.New, fmt.Errorf without %w).
//
// corruptObjectDeletedError is unexported in k8s.io/apiserver/pkg/storage/etcd3; the copy below
// has the same declaration (watcher.go:872-879 at the pinned apiserver): a struct with one error
// field, Error and Unwrap on the pointer receiver. As only compares the dynamic type with the
// target's element type, so the copy is a faithful stand-in.

import (
	"context"
	"errors"
	"fmt"
	"reflect"
	"testing"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	apierrors "k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/runtime/schema"
)

type corruptObjectDeletedError struct {
	err error
}

func (e *corruptObjectDeletedError) Error() string {
	return fmt.Sprintf("saw a DELETED event, but object data is corrupt - %v", e.err)
}
func (e *corruptObjectDeletedError) Unwrap() error { return e.err }

// isLeaf is Lean's errors.isLeafError: no As(any) bool, no Unwrap() error, no Unwrap() []error.
func isLeaf(err error) bool {
	_, u := err.(interface{ Unwrap() error })
	_, us := err.(interface{ Unwrap() []error })
	_, as := err.(interface{ As(any) bool })
	return !u && !us && !as
}

func asLeafTyCases() []struct {
	name string
	err  error
	ty   string
} {
	return []struct {
		name string
		err  error
		ty   string
	}{
		{"status.Error", status.Error(codes.Unavailable, "x"), "*status.Error"},
		{"rpctypes.ErrGRPCCompacted", rpctypes.ErrGRPCCompacted, "*status.Error"},
		{"rpctypes.Error(ErrGRPCCompacted)", rpctypes.Error(rpctypes.ErrGRPCCompacted), "rpctypes.EtcdError"},
		{"rpctypes.ErrCompacted", rpctypes.ErrCompacted, "rpctypes.EtcdError"},
		{"rpctypes.ErrFutureRev", rpctypes.ErrFutureRev, "rpctypes.EtcdError"},
		{"context.DeadlineExceeded", context.DeadlineExceeded, "context.deadlineExceededError"},
		{"context.Canceled", context.Canceled, "*errors.errorString"},
		{"NewResourceExpired", apierrors.NewResourceExpired("x"), "*errors.StatusError"},
		{"NewTooManyRequests", apierrors.NewTooManyRequests("x", 1), "*errors.StatusError"},
		{"NewNotFound", apierrors.NewNotFound(schema.GroupResource{}, "x"), "*errors.StatusError"},
		{"errors.New", errors.New("x"), "*errors.errorString"},
		{"fmt.Errorf no %w", fmt.Errorf("a %q %d %s", "k", 3, "t"), "*errors.errorString"},
	}
}

// TestAsLeafTyWatcherErrors: each type the watcher's producers send is a leaf of the expected
// dynamic type, outside *corruptObjectDeletedError's type set (a non-interface target: its only
// member is itself, and the underlying types differ), and errors.As returns false with the target
// unchanged (a sentinel non-nil value, to see a write).
func TestAsLeafTyWatcherErrors(t *testing.T) {
	sentinel := &corruptObjectDeletedError{err: errors.New("sentinel")}
	target := reflect.TypeOf(sentinel)
	for _, c := range asLeafTyCases() {
		got := reflect.TypeOf(c.err)
		if got.String() != c.ty {
			t.Errorf("%s: dynamic type %v, want %s", c.name, got, c.ty)
		}
		if !isLeaf(c.err) {
			t.Errorf("%s: not a leaf error (has As or Unwrap)", c.name)
		}
		if got.AssignableTo(target) || got == target || (got.Kind() == reflect.Pointer && got.Elem() == target.Elem()) {
			t.Errorf("%s: type in the target's type set", c.name)
		}
		v := sentinel
		if errors.As(c.err, &v) {
			t.Errorf("%s: errors.As returned true", c.name)
		}
		if v != sentinel {
			t.Errorf("%s: target written", c.name)
		}
		// the nil-target-value form the watcher uses
		var w *corruptObjectDeletedError
		if errors.As(c.err, &w) || w != nil {
			t.Errorf("%s: errors.As with a nil target value returned true or wrote it", c.name)
		}
	}
}

// TestAsLeafTyNegatives: the premises matter. A wrapper (Unwrap) of a *corruptObjectDeletedError,
// an error with an As method, and the target's own type give true.
func TestAsLeafTyNegatives(t *testing.T) {
	inner := &corruptObjectDeletedError{err: errors.New("x")}
	var w *corruptObjectDeletedError
	if !errors.As(fmt.Errorf("wrap: %w", inner), &w) || w != inner {
		t.Errorf("a wrapping error: errors.As did not find the wrapped one")
	}
	w = nil
	if !errors.As(liarAs{}, &w) {
		t.Errorf("an error with As: errors.As did not ask it")
	}
	w = nil
	if !errors.As(inner, &w) || w != inner {
		t.Errorf("the target's own type: errors.As returned false")
	}
}

type liarAs struct{}

func (liarAs) Error() string { return "liar" }
func (liarAs) As(x any) bool { return true }
