// Package hasstatuscause is the Go counterexample to the trust-boundary axiom
// apierrors.HasStatusCause.wp_proof (Spec/k8s_io/apimachinery/pkg/api/errors/HasStatusCause.lean;
// found 2026-11-17 by the k8s 7g step-1 attack, notes/axiom-review/k8s-7g-trust.md on branch k8s-7g).
// The spec's precondition apiErrOk err holds the *StatusError struct read-only but not its details;
// its post is □ ∀ w, apiErrAt err w -∗ ⌜b = causeIn cs name⌝, a fact about every view of the error
// built at any later time. A caller that still owns the details (a non-read-only
// *metav1.StatusDetails) writes their causes after the call, then persists them and builds the view
// .status st [{Type: "X"}]: the post gives b = true, but Go returned false (the causes were empty when
// HasStatusCause read them). The program below panics in Go and has a provable no-panic triple from
// the axiom. Tests only, no Goose project.
package hasstatuscause

import (
	"testing"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
)

// HasStatusCauseLater: the proof persists dp and its causes after the write, builds
// apiErrAt err (.status st [{Type: "X"}]), applies the post and concludes b = true.
func HasStatusCauseLater() {
	dp := &metav1.StatusDetails{}
	se := &apierrors.StatusError{ErrStatus: metav1.Status{Details: dp}}
	var err error = se
	b := apierrors.HasStatusCause(err, "X")
	dp.Causes = []metav1.StatusCause{{Type: "X"}}
	if !b {
		panic("claim: HasStatusCause")
	}
}

func TestLaterView(t *testing.T) {
	defer func() {
		r := recover()
		t.Logf("HasStatusCauseLater: recovered %v", r)
		if r == nil {
			t.Errorf("HasStatusCauseLater: no panic")
		}
	}()
	HasStatusCauseLater()
}
