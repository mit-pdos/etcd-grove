// Package apierrorsdetails backs the restated trust-boundary axioms apierrors.NewConflict.wp_proof
// and apierrors.NewInternalError.wp_proof (stage apierrors-fix, 2026-11-17; HasStatusCause fix (a),
// notes/hasstatuscause-later-view.md): what each constructor sets in the returned *StatusError's
// status, its details in particular (errors.go:232-244, 387-397 at examples/k8s/etcd3/go.mod's
// k8s.io/apimachinery), and which arguments make it panic.
package apierrorsdetails

import (
	"errors"
	"fmt"
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

// NewConflict: Failure/Conflict/409, Details non-nil with no causes (nil Causes). These errors meet
// fmt.argOk (nil, or no Format and an Error() that returns), or show a single panic is recovered.
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

// The attack of 2026-11-17 (notes/axiom-review/apierrors-fix.md; /shared/tmp/apierrors-attack/cx):
// fmt's catchPanic re-panics when the recovered value's own Error() panics (print.go:591-594), and
// handleMethods calls Format in place of Error() (print.go:630-634). So NewConflict needs fmt.argOk
// of err (the precondition-free text was false) and NewInternalError needs no Format method (the
// first restatement, with only Error()'s spec, was false); a plain panicking Format is recovered.
type badPanic struct{}

func (badPanic) Error() string { panic("again") }

type nestErr struct{}

func (nestErr) Error() string { panic(badPanic{}) }

type fmtErr struct{}

func (fmtErr) Error() string                 { return "ok" }
func (fmtErr) Format(f fmt.State, verb rune) { panic(badPanic{}) }

type simpleFmt struct{}

func (simpleFmt) Error() string                 { return "ok" }
func (simpleFmt) Format(f fmt.State, verb rune) { panic("x") }

func TestNestedPanics(t *testing.T) {
	if !panics(func() { apierrors.NewConflict(gr, "n", nestErr{}) }) {
		t.Errorf("NewConflict(nestErr): no panic")
	}
	if !panics(func() { apierrors.NewConflict(gr, "n", fmtErr{}) }) {
		t.Errorf("NewConflict(fmtErr): no panic")
	}
	if !panics(func() { apierrors.NewInternalError(fmtErr{}) }) {
		t.Errorf("NewInternalError(fmtErr): no panic")
	}
	if panics(func() { apierrors.NewInternalError(simpleFmt{}) }) {
		t.Errorf("NewInternalError(simpleFmt): panics")
	}
}
