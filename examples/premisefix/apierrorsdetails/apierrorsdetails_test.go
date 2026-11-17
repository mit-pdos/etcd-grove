// Package apierrorsdetails backs the restated trust-boundary axioms apierrors.NewConflict.wp_proof
// and apierrors.NewInternalError.wp_proof (stage apierrors-fix, 2026-11-17; HasStatusCause fix (a),
// notes/hasstatuscause-later-view.md): what each constructor sets in the returned *StatusError's
// status, its details in particular (errors.go:232-244, 387-397 at examples/k8s/etcd3/go.mod's
// k8s.io/apimachinery), and which arguments make it panic.
package apierrorsdetails

import (
	"errors"
	"testing"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/runtime/schema"
)

type panicErr struct{}

func (panicErr) Error() string { panic("Error() panics") }

var gr = schema.GroupResource{Group: "apps", Resource: "daemonsets"}

func panics(f func()) (p bool) {
	defer func() { p = recover() != nil }()
	f()
	return false
}

func checkStatus(t *testing.T, name string, st metav1.Status, reason metav1.StatusReason, code int32) {
	if st.Status != metav1.StatusFailure || st.Reason != reason || st.Code != code {
		t.Errorf("%s: status %q reason %q code %d", name, st.Status, st.Reason, st.Code)
	}
	if st.Details == nil {
		t.Fatalf("%s: Details is nil", name)
	}
}

// NewConflict: Failure/Conflict/409, Details non-nil with no causes (nil Causes); no precondition:
// it never calls err.Error() itself, and fmt's %v recovers a panicking Error and prints nil.
func TestNewConflict(t *testing.T) {
	for _, err := range []error{nil, errors.New("e"), panicErr{}} {
		var se *apierrors.StatusError
		if panics(func() { se = apierrors.NewConflict(gr, "n", err) }) {
			t.Fatalf("NewConflict(%T) panics", err)
		}
		checkStatus(t, "NewConflict", se.ErrStatus, metav1.StatusReasonConflict, 409)
		if se.ErrStatus.Details.Causes != nil {
			t.Errorf("NewConflict: Causes %v, want nil", se.ErrStatus.Details.Causes)
		}
		if apierrors.HasStatusCause(se, "") {
			t.Errorf("NewConflict: HasStatusCause(\"\") true")
		}
	}
}

// NewInternalError: Failure/InternalError/500, Details non-nil with exactly one cause, of type ""
// and message err.Error(); it calls err.Error() directly, so a nil err or a panicking Error panics.
func TestNewInternalError(t *testing.T) {
	if !panics(func() { apierrors.NewInternalError(nil) }) {
		t.Errorf("NewInternalError(nil): no panic")
	}
	if !panics(func() { apierrors.NewInternalError(panicErr{}) }) {
		t.Errorf("NewInternalError(panicErr): no panic")
	}
	se := apierrors.NewInternalError(errors.New("boom"))
	checkStatus(t, "NewInternalError", se.ErrStatus, metav1.StatusReasonInternalError, 500)
	cs := se.ErrStatus.Details.Causes
	if len(cs) != 1 || cs[0].Type != "" || cs[0].Message != "boom" || cs[0].Field != "" {
		t.Errorf("NewInternalError: Causes %#v", cs)
	}
	if !apierrors.HasStatusCause(se, "") || apierrors.HasStatusCause(se, "X") {
		t.Errorf("NewInternalError: HasStatusCause")
	}
}
