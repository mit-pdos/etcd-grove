// Package recordetcdrequest checks the premise of metrics.RecordEtcdRequest's trust-boundary spec
// (premise fixes 3, 2026-11-10; Spec/k8s_io/apiserver/pkg/storage/etcd3/metrics/RecordEtcdRequest.lean):
// the spec said it returns for every err, but for a non-nil err RecordEtcdRequest computes
// errorReason(err) (metrics.go:220-221), which calls errors.Is, errors.As and grpc's
// status.FromError on it (metrics.go:225-243), whether the metrics are registered or not.
// FromError calls the error's GRPCStatus, which for a typed-nil *status.Error (grpc's
// internal/status.Error) dereferences nil: a panic. The spec now requires statusErrOk err
// (nil, or a leaf whose Error, GRPCStatus and Is return), which excludes it; the store's errors
// (the client's, and ErrTransactionConflict, an errors.New leaf) have it.
// Found by etcd-grove-81's independent review.
package recordetcdrequest

import (
	"errors"
	"reflect"
	"testing"
	"time"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/storage/etcd3/metrics"
)

var gr = schema.GroupResource{Group: "", Resource: "pods"}

func record(err error) (panicked any) {
	defer func() { panicked = recover() }()
	metrics.RecordEtcdRequest("get", gr, err, time.Now())
	return nil
}

// A typed-nil *status.Error (the dynamic type status.Error returns, zeroed): non-nil as an error.
func typedNilStatusError(t *testing.T) error {
	t.Helper()
	ty := reflect.TypeOf(status.Error(codes.Internal, "x"))
	if ty.Kind() != reflect.Pointer {
		t.Fatalf("expected status.Error to return a pointer, got %v", ty)
	}
	err, ok := reflect.Zero(ty).Interface().(error)
	if !ok || err == nil {
		t.Fatalf("expected a non-nil error holding a nil %v", ty)
	}
	return err
}

func TestRecordEtcdRequestTypedNilStatusErrorPanics(t *testing.T) {
	if p := record(typedNilStatusError(t)); p == nil {
		t.Fatalf("expected RecordEtcdRequest to panic on a typed-nil *status.Error (metrics are not registered)")
	} else {
		t.Logf("panicked, as the premise statusErrOk excludes: %v", p)
	}
}

// The errors the store passes return: nil, ErrTransactionConflict (txnError), a status error
// (the client's), an errors.New leaf.
func TestRecordEtcdRequestStoreErrorsReturn(t *testing.T) {
	for _, err := range []error{nil, metrics.ErrTransactionConflict,
		status.Error(codes.Unavailable, "etcdserver: request timed out"), errors.New("leaf")} {
		if p := record(err); p != nil {
			t.Fatalf("RecordEtcdRequest(%v) panicked: %v", err, p)
		}
	}
}

// ErrTransactionConflict, which txnError returns for a failed comparison, is
// errors.New("transaction conflict") (metrics.go:42 at the apiserver pin 9c4ec15b8038): what the
// restated trust-boundary axiom ErrTransactionConflict_init (errorsNewVarInit) says. Its dynamic
// type is *errors.errorString, a leaf with Error only: no Unwrap, As, Is or GRPCStatus method
// (EtcdGrove.ErrorStringLeaf), so statusErrOk holds of it.
func TestErrTransactionConflictIsErrorsNew(t *testing.T) {
	e := metrics.ErrTransactionConflict
	if got := e.Error(); got != "transaction conflict" {
		t.Fatalf("expected the message %q, got %q", "transaction conflict", got)
	}
	ty := reflect.TypeOf(e)
	if want := reflect.TypeOf(errors.New("x")); ty != want {
		t.Fatalf("expected the dynamic type %v (errors.New's), got %v", want, ty)
	}
	if ty.String() != "*errors.errorString" {
		t.Fatalf("expected *errors.errorString, got %v", ty)
	}
	for _, m := range []string{"Unwrap", "As", "Is", "GRPCStatus"} {
		if _, ok := ty.MethodByName(m); ok {
			t.Fatalf("expected no %s method on %v", m, ty)
		}
	}
	if ty.NumMethod() != 1 {
		t.Fatalf("expected Error as the only method of %v, got %d methods", ty, ty.NumMethod())
	}
}
