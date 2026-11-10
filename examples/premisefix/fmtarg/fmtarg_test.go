// Package fmtarg checks which method fmt calls on an argument (premise fixes 4, fix 5, 2026-11-10),
// what fmt.argOk (Spec/fmt/Errorf.lean) assumes: for %v/%s fmt calls Format when the type has one
// (in place of Error or String), and Error in place of String when the type is an error; so a
// String method's spec says what fmt does only for a type with neither Format nor Error, and an
// Error method's only for a type without Format. A method fmt calls that panics with a value whose
// Error panics makes Sprintf panic (fmt re-raises a nested panic). Found by the round-2 premise
// attack (fmt-argOk-error-over-string-and-formatter).
package fmtarg

import (
	"fmt"
	"testing"
)

type boom struct{}

func (boom) Error() string { panic("nested") }

// String returns "s", Format panics: fmt calls Format.
type withFormat struct{}

func (withFormat) String() string             { return "s" }
func (withFormat) Format(f fmt.State, c rune) { panic(boom{}) }

// Error returns "e", Format panics: fmt calls Format.
type errWithFormat struct{}

func (errWithFormat) Error() string              { return "e" }
func (errWithFormat) Format(f fmt.State, c rune) { panic(boom{}) }

// String returns "s", Error panics: fmt calls Error.
type stringerAndError struct{}

func (stringerAndError) String() string { return "s" }
func (stringerAndError) Error() string  { panic(boom{}) }

// String alone, Error alone: called.
type stringer struct{}

func (stringer) String() string { return "s" }

type errOnly struct{}

func (errOnly) Error() string { return "e" }

func panics(f func()) (p bool) {
	defer func() { p = recover() != nil }()
	f()
	return
}

func TestMethodCalled(t *testing.T) {
	for _, verb := range []string{"%v", "%s"} {
		for _, c := range []struct {
			name  string
			arg   any
			panic bool
			out   string
		}{
			{"String with Format", withFormat{}, true, ""},
			{"Error with Format", errWithFormat{}, true, ""},
			{"String with Error", stringerAndError{}, true, ""},
			{"String alone", stringer{}, false, "s"},
			{"Error alone", errOnly{}, false, "e"},
		} {
			var out string
			p := panics(func() { out = fmt.Sprintf(verb, c.arg) })
			if p != c.panic || (!p && out != c.out) {
				t.Errorf("%s %s: panic %v, output %q; want panic %v, output %q", verb, c.name, p, out, c.panic, c.out)
			}
		}
	}
	// %w (Errorf): Error with Format calls Format too
	if !panics(func() { _ = fmt.Errorf("%w", errWithFormat{}) }) {
		t.Errorf("Errorf %%w of an error with Format: no panic")
	}
}
