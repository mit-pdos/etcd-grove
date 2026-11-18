// Package errorfplain is the Go counterexample to the trust-boundary axiom fmt.ErrorfPlain.wp_proof
// (Spec/fmt/ErrorfPlain.lean; found 2026-11-15 by k8s 7f-5a-P while applying the approved E3 text,
// notes/k8s-7f5a-draft.md §11.3): its premise is `¬ List.IsInfix "%w" format` with
// fmt.argsOk fmt.errorfVerbs format xs, and its post says the result is an *errors.errorString.
// A w directive with flags, width or precision (%+w, %-5w, % w, %#w, %05.2w) has no "%w" infix and
// parses (fmt.fmtDirectives gives a w directive, which argsOk admits with an error argument), but
// Go's doPrintf records a wrap for every w verb (fmt/print.go:1051, 1146): Errorf returns a
// *fmt.wrapError, which errors.Is sees through. A program the axiom lets one prove panic-free
// (errors.Is of a leaf errorString against io.EOF is false) panics. Latent: the axiom's two callers
// (rafthttp checkPostResponse, streamReader.dial) pass formats with no w verb at all.
// Tests only, no Goose project.
package errorfplain

import (
	"errors"
	"fmt"
	"io"
	"reflect"
	"strings"
	"testing"
)

func TestFlaggedWVerbWraps(t *testing.T) {
	errorString := reflect.TypeOf(errors.New(""))
	for _, f := range []string{"%+w", "%-5w", "% w", "%#w", "%05.2w", "x %+w y"} {
		if strings.Contains(f, "%w") {
			t.Fatalf("%q contains %%w: not a counterexample format", f)
		}
		args := []any{io.EOF}
		err := fmt.Errorf(f, args...)
		if reflect.TypeOf(err) == errorString {
			t.Errorf("Errorf(%q, io.EOF) is an *errors.errorString: the axiom would be right", f)
		}
		if !errors.Is(err, io.EOF) {
			t.Errorf("Errorf(%q, io.EOF): errors.Is(_, io.EOF) false", f)
		}
	}
}

// The program the axiom proves panic-free: an *errors.errorString leaf is not io.EOF under errors.Is.
func TestProgramPanics(t *testing.T) {
	defer func() {
		if recover() == nil {
			t.Fatal("did not panic")
		}
	}()
	f, args := "%+w", []any{io.EOF}
	if err := fmt.Errorf(f, args...); errors.Is(err, io.EOF) {
		panic("wrapped")
	}
}
