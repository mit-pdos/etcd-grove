// Package apierrorstypednil is the Go counterexample to four named hypotheses of client-go cache's
// Link (Proof/k8s_io/client_go/tools/cache/Link.lean): apierrors.IsTooManyRequests.spec,
// IsGone.spec, IsInternalError.spec and IsResourceExpired.spec
// (Spec/k8s_io/apimachinery/pkg/api/errors/<F>.lean; found 2026-11-17, k8s 7g step 1 for
// IsTooManyRequests, soundness-1117 for the other three). Each has no precondition and returns
// "some boolean". On a typed nil *StatusError each panics in Go: ReasonForError's err.(APIStatus)
// succeeds and (*StatusError).Status() dereferences the nil receiver, as found for IsTimeout on
// 2026-11-10 (examples/k8s7e2attack TestTypedNilStatusError). Tests only, no Goose project.
package apierrorstypednil

import (
	"errors"
	"testing"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
)

func expectPanic(t *testing.T, name string, f func(error) bool) {
	defer func() {
		r := recover()
		t.Logf("%s: recovered %v", name, r)
		if r == nil {
			t.Errorf("%s: no panic", name)
		}
	}()
	var se *apierrors.StatusError
	var err error = se
	f(err)
}

func TestTypedNil(t *testing.T) {
	expectPanic(t, "IsTooManyRequests", apierrors.IsTooManyRequests)
	expectPanic(t, "IsGone", apierrors.IsGone)
	expectPanic(t, "IsInternalError", apierrors.IsInternalError)
	expectPanic(t, "IsResourceExpired", apierrors.IsResourceExpired)
}

// TestNilAndViews checks the restated specs (apierrors-fix, 2026-11-17): on nil each returns false
// without panicking (their precondition admits nil), and on a *StatusError each answers its
// per-view formula (IsTooManyRequests: reason TooManyRequests or code 429, whatever the reason;
// IsGone/IsInternalError: their reason, or an unknown reason and 410/500; IsResourceExpired: reason
// Expired); on a plain error, false.
func TestNilAndViews(t *testing.T) {
	fs := map[string]func(error) bool{"IsTooManyRequests": apierrors.IsTooManyRequests,
		"IsGone": apierrors.IsGone, "IsInternalError": apierrors.IsInternalError,
		"IsResourceExpired": apierrors.IsResourceExpired}
	for n, f := range fs {
		if f(nil) {
			t.Errorf("%s(nil) = true", n)
		}
		if f(errors.New("x")) {
			t.Errorf("%s(plain) = true", n)
		}
	}
	mk := func(reason metav1.StatusReason, code int32) error {
		return &apierrors.StatusError{ErrStatus: metav1.Status{Reason: reason, Code: code}}
	}
	cases := []struct {
		f    string
		e    error
		want bool
	}{
		{"IsTooManyRequests", mk(metav1.StatusReasonConflict, 429), true},
		{"IsTooManyRequests", mk(metav1.StatusReasonTooManyRequests, 0), true},
		{"IsGone", mk(metav1.StatusReasonConflict, 410), false},
		{"IsGone", mk("Unlisted", 410), true},
		{"IsGone", mk(metav1.StatusReasonGone, 0), true},
		{"IsInternalError", mk(metav1.StatusReasonConflict, 500), false},
		{"IsInternalError", mk("", 500), true},
		{"IsResourceExpired", mk(metav1.StatusReasonExpired, 0), true},
		{"IsResourceExpired", mk(metav1.StatusReasonGone, 410), false},
	}
	for _, c := range cases {
		if got := fs[c.f](c.e); got != c.want {
			t.Errorf("%s(%v) = %v, want %v", c.f, c.e, got, c.want)
		}
	}
}
