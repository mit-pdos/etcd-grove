package watcherctx

// prove-k8s2 (2026-11-20): the Go evidence for the trusted text errors.AsNoMatch
// (Spec/errors/AsNoMatch.lean), which generalizes errors.AsLeafTy (asleafty_test.go) to depth one:
// errors.As(err, &target) returns false, the target unchanged, for nil, for a leaf outside the target's
// type set, and for a wrapper outside it (Unwrap() error, no As method) whose Unwrap returns nil or
// such a leaf; Unwrap is called exactly once. The APIStatus checks of apimachinery's api/errors call
// errors.As(err, &status) with an interface target (APIStatus) on such wrappers
// (*storage.StorageError, examples/k8s/etcd3/trustspecs_test.go TestStatusChecksPlain).

import (
	"errors"
	"testing"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
)

// countWrap is a wrapper outside APIStatus's type set: Unwrap() error, no As, counting its calls.
type countWrap struct {
	inner error
	calls *int
}

func (w countWrap) Error() string { return "wrap" }
func (w countWrap) Unwrap() error  { *w.calls++; return w.inner }

func TestAsNoMatchWrapper(t *testing.T) {
	for _, inner := range []error{nil, errors.New("x")} {
		n := 0
		e := countWrap{inner: inner, calls: &n}
		if !isLeaf(errors.New("x")) || isLeaf(e) {
			t.Fatalf("leaf classification")
		}
		// an interface target (APIStatus, as the api/errors checks), its value a sentinel
		var sentinel apierrors.APIStatus = apierrors.NewResourceExpired("sentinel")
		v := sentinel
		if errors.As(e, &v) {
			t.Errorf("inner %v: errors.As returned true (interface target)", inner)
		}
		if v != sentinel {
			t.Errorf("inner %v: target written (interface target)", inner)
		}
		if n != 1 {
			t.Errorf("inner %v: Unwrap called %d times, want 1", inner, n)
		}
		// a non-interface target of another underlying type
		n = 0
		w := &corruptObjectDeletedError{err: errors.New("sentinel")}
		w0 := w
		if errors.As(e, &w) || w != w0 {
			t.Errorf("inner %v: errors.As returned true or wrote the target (pointer target)", inner)
		}
		if n != 1 {
			t.Errorf("inner %v: Unwrap called %d times, want 1 (pointer target)", inner, n)
		}
	}
	// nil: false, the target unchanged
	var s apierrors.APIStatus
	if errors.As(nil, &s) || s != nil {
		t.Errorf("nil: errors.As returned true or wrote the target")
	}
}

// TestAsNoMatchNegatives: a wrapper over an APIStatus finds it (the premise that the unwrapped
// error is a non-matching leaf matters).
func TestAsNoMatchNegatives(t *testing.T) {
	n := 0
	inner := apierrors.NewResourceExpired("x")
	var s apierrors.APIStatus
	if !errors.As(countWrap{inner: inner, calls: &n}, &s) || s != apierrors.APIStatus(inner) {
		t.Errorf("a wrapper of a *StatusError: errors.As did not find it")
	}
}
