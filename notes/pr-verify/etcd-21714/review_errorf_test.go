package clientv3

import (
	"errors"
	"fmt"
	"testing"
)

// fmtErr has a pure Error() (what Spec/fmt/ErrorfWrap.lean's premise, stringMethodSpec err "Error",
// covers) but also a Format method with an effect: fmt.Errorf's %w calls Format, not Error.
type fmtErr struct{ calls *int }

func (e fmtErr) Error() string { return "inner" }
func (e fmtErr) Format(s fmt.State, verb rune) {
	*e.calls++
	fmt.Fprintf(s, "formatted(%c)", verb)
}

func TestReviewErrorfWrapCallsFormat(t *testing.T) {
	n := 0
	inner := fmtErr{&n}
	e := fmt.Errorf("etcdclient: dialing [%s] failed: %w", "a;b", inner)
	t.Logf("e.Error() = %q, Format calls = %d", e.Error(), n)
	t.Logf("errors.Unwrap(e) == inner: %v; type %T", errors.Unwrap(e) == error(inner), e)
	if n == 0 {
		t.Fatal("Format not called")
	}
}
