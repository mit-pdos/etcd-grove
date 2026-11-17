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
	"testing"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
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
