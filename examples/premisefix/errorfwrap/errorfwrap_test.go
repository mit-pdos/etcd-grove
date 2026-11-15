// Package errorfwrap is the Go evidence of the E3 text (k8s 7f-5a-P, notes/k8s-7f5a-draft.md §11.3):
// fmt.Errorf.spec gains, for a format whose parsed directives (fmt.fmtDirectives,
// Spec/fmt/Errorf.lean) are some ds with no verb w, that the result is a fresh *errors.errorString.
//
// Go (go1.27.3, fmt/errors.go): Errorf returns errors.New(format) when errorf needs no formatting
// (no argument and no %), and otherwise errorf returns errors.New(s) when p.wrappedErrs is empty, a
// *fmt.wrapError for one %w target and a *fmt.wrapErrors for several. doPrintf (fmt/print.go:1051,
// 1146) appends to wrappedErrs exactly at a directive whose verb is w and that has an argument,
// whatever the flags, width, precision or argument index, and whatever the argument's type: %[1]w,
// %+w, %-5w all wrap, a non-error argument too (TestWVerbFormsWrap). A %w with no argument left does
// not wrap (TestMissingArgNoWrap): the spec's premise excludes it anyway (a w directive), so the
// premise is conservative there.
//
//   - TestWatcherFormats: the watcher's fmt.Errorf calls on its error paths, with the formats copied
//     from k8s.io/apiserver at the 7f pin (parseEvent's event.go:69, syncPaginated's watcher.go:354,
//     GetCurrentResourceVersion's store.go:742): *errors.errorString, fresh per call;
//   - TestWVerbFormsWrap: %w, %[1]w, %+w, %-5w, %#w, % w, %05.2w, a non-error argument under %w, and
//     two %w: a wrap (*fmt.wrapError, *fmt.wrapErrors), never *errors.errorString;
//   - TestDirectivesPortExamples: fmtDirectives below is a transcription of fmt.fmtDirectivesAux; it
//     gives the Lean file's examples (the `example`s after fmt.fmtDirectives);
//   - TestNoWDirectiveGivesErrorString: a randomized differential test, 200000 formats over an
//     alphabet of verbs, flags, digits, ., *, [, ], %, w, a multi-byte rune and invalid UTF-8, with
//     0-3 arguments (errors and non-errors): whenever fmtDirectives gives some ds with no verb w, the
//     result is a *errors.errorString; it also counts the formats with a w directive that wrap (most).
package errorfwrap

import (
	"errors"
	"fmt"
	"math/rand"
	"reflect"
	"testing"
)

// directive mirrors fmt.Directive.
type directive struct {
	verb   byte
	sharpV bool
}

type phase int

const (
	phFlags phase = iota
	phWidth
	phPrec
)

const maxNumDigits = 7 // fmt.maxNumDigits

// fmtDirectives transcribes fmt.fmtDirectivesAux (Spec/fmt/Errorf.lean) over the format's bytes:
// ok = false is the Lean none.
func fmtDirectives(format string) ([]directive, bool) {
	return aux(false, false, phFlags, 0, []byte(format))
}

// aux(in, sharp, ph, n, bs): in = false is st = none; otherwise st = some (sharp, ph) with n the
// digits read in the width or precision phase.
func aux(in, sharp bool, ph phase, n int, bs []byte) ([]directive, bool) {
	if len(bs) == 0 {
		return []directive{}, true
	}
	b, rest := bs[0], bs[1:]
	if !in {
		if b == '%' {
			return aux(true, false, phFlags, 0, rest)
		}
		return aux(false, false, phFlags, 0, rest)
	}
	verb := func() ([]directive, bool) {
		if b == '*' || b == '[' {
			return nil, false
		}
		if b == '%' {
			return aux(false, false, phFlags, 0, rest)
		}
		ds, ok := aux(false, false, phFlags, 0, rest)
		if !ok {
			return nil, false
		}
		return append([]directive{{b, sharp && b == 'v'}}, ds...), true
	}
	digit := '0' <= b && b <= '9'
	switch ph {
	case phFlags:
		switch {
		case b == '#':
			return aux(true, true, phFlags, 0, rest)
		case b == '+' || b == '-' || b == '0' || b == ' ':
			return aux(true, sharp, phFlags, 0, rest)
		case digit:
			return aux(true, sharp, phWidth, 1, rest)
		case b == '.':
			return aux(true, sharp, phPrec, 0, rest)
		}
		return verb()
	case phWidth:
		switch {
		case digit:
			if n < maxNumDigits {
				return aux(true, sharp, phWidth, n+1, rest)
			}
			return nil, false
		case b == '.':
			return aux(true, sharp, phPrec, 0, rest)
		}
		return verb()
	default: // phPrec
		if digit {
			if n < maxNumDigits {
				return aux(true, sharp, phPrec, n+1, rest)
			}
			return nil, false
		}
		return verb()
	}
}

func hasW(ds []directive) bool {
	for _, d := range ds {
		if d.verb == 'w' {
			return true
		}
	}
	return false
}

var errorStringType = reflect.TypeOf(errors.New(""))

func TestDirectivesPortExamples(t *testing.T) {
	type ex struct {
		f    string
		ds   []directive
		some bool
	}
	exs := []ex{
		{"%w: Limit(%d) not supported", []directive{{'w', false}, {'d', false}}, true},
		{"%%d %5.2f %#v", []directive{{'f', false}, {'v', true}}, true},
		{"%#x %+v %-08.3s %.q % d", []directive{{'x', false}, {'v', false}, {'s', false}, {'q', false}, {'d', false}}, true},
		{"%*d", nil, false},
		{"%5.*d", nil, false},
		{"%[1]d", nil, false},
		{"abc%", []directive{}, true},
		{"%5%%s", []directive{{'s', false}}, true},
		{"unexpected conf type %d", []directive{{'d', false}}, true},
		{"%1234567d|%.9999999d", []directive{{'d', false}, {'d', false}}, true},
		{"rev %99999999d", nil, false},
		{"rev %.99999999d", nil, false},
		{"%000000000005d", []directive{{'d', false}}, true},
	}
	for _, e := range exs {
		ds, ok := fmtDirectives(e.f)
		if ok != e.some || (ok && !reflect.DeepEqual(ds, e.ds)) {
			t.Errorf("fmtDirectives(%q) = %v, %v; the Lean example says %v, %v", e.f, ds, ok, e.ds, e.some)
		}
	}
}

func TestWatcherFormats(t *testing.T) {
	calls := []struct {
		where string
		mk    func() error
	}{
		{"parseEvent (event.go:69)", func() error {
			return fmt.Errorf("etcd event received with PrevKv=nil (key=%q, modRevision=%d, type=%s)", string([]byte("/registry/pods/a")), int64(7), "DELETE")
		}},
		{"syncPaginated (watcher.go:354)", func() error {
			return fmt.Errorf("no results were found, but etcd indicated there were more values remaining")
		}},
		{"GetCurrentResourceVersion (store.go:742)", func() error {
			return fmt.Errorf("the current resource version must be greater than 0")
		}},
	}
	for _, c := range calls {
		e1, e2 := c.mk(), c.mk()
		if reflect.TypeOf(e1) != errorStringType {
			t.Errorf("%s: %T, want *errors.errorString", c.where, e1)
		}
		if e1 == e2 {
			t.Errorf("%s: two calls return the same pointer", c.where)
		}
	}
	for _, f := range []string{
		"etcd event received with PrevKv=nil (key=%q, modRevision=%d, type=%s)",
		"no results were found, but etcd indicated there were more values remaining",
		"the current resource version must be greater than 0",
	} {
		if ds, ok := fmtDirectives(f); !ok || hasW(ds) {
			t.Errorf("fmtDirectives(%q) = %v, %v: the E3 premise does not hold of the watcher's format", f, ds, ok)
		}
	}
}

func TestWVerbFormsWrap(t *testing.T) {
	base := errors.New("base")
	cases := []struct {
		f    string
		args []any
	}{
		{"%w", []any{base}},
		{"%[1]w", []any{base}},
		{"%+w", []any{base}},
		{"%-5w", []any{base}},
		{"%#w", []any{base}},
		{"% w", []any{base}},
		{"%05.2w", []any{base}},
		{"%w", []any{42}}, // a non-error argument: still a wrap (with a nil Unwrap)
		{"%w and %w", []any{base, errors.New("other")}},
		{"%[2]w %[1]d", []any{1, base}},
	}
	for _, c := range cases {
		err := fmt.Errorf(c.f, c.args...)
		if reflect.TypeOf(err) == errorStringType {
			t.Errorf("Errorf(%q): *errors.errorString, want a wrap", c.f)
		}
		switch err.(type) {
		case interface{ Unwrap() error }, interface{ Unwrap() []error }:
		default:
			t.Errorf("Errorf(%q): %T has no Unwrap", c.f, err)
		}
	}
}

func TestMissingArgNoWrap(t *testing.T) {
	f, noArgs := "x %w", []any{} // variables: vet refuses the literal call
	err := fmt.Errorf(f, noArgs...)
	if reflect.TypeOf(err) != errorStringType || err.Error() != "x %!w(MISSING)" {
		t.Errorf("Errorf(\"x %%w\"): %T %q", err, err)
	}
	if ds, ok := fmtDirectives("x %w"); !ok || !hasW(ds) {
		t.Errorf("fmtDirectives(\"x %%w\") = %v, %v: expected a w directive (excluded by the premise)", ds, ok)
	}
}

type strArg struct{}

func (strArg) String() string { return "s" }

func TestNoWDirectiveGivesErrorString(t *testing.T) {
	alphabet := []string{"%", "%", "%", "w", "w", "v", "d", "s", "q", "x", "#", "+", "-", " ", "0", "1", "5", "9",
		".", "*", "[", "]", "2", "a", "é", "\xff", "\xe2", "%%", "%w", "%[1]w", "%+w", "%-5w"}
	argPool := []any{errors.New("e1"), fmt.Errorf("e2: %w", errors.New("inner")), 7, "str", strArg{}, nil, 3.5}
	rng := rand.New(rand.NewSource(1))
	var noW, noWStr, withW, withWWrap, refused int
	for i := 0; i < 200000; i++ {
		n := rng.Intn(10)
		f := ""
		for j := 0; j < n; j++ {
			f += alphabet[rng.Intn(len(alphabet))]
		}
		args := make([]any, rng.Intn(4))
		for j := range args {
			args[j] = argPool[rng.Intn(len(argPool))]
		}
		err := fmt.Errorf(f, args...)
		ds, ok := fmtDirectives(f)
		switch {
		case !ok:
			refused++
		case !hasW(ds):
			noW++
			if reflect.TypeOf(err) != errorStringType {
				t.Fatalf("Errorf(%q, %v): %T, but fmtDirectives = %v has no w", f, args, err, ds)
			}
			noWStr++
		default:
			withW++
			if reflect.TypeOf(err) != errorStringType {
				withWWrap++
			}
		}
	}
	t.Logf("no w directive: %d (all *errors.errorString: %d); a w directive: %d (%d wrap); refused by the parser: %d",
		noW, noWStr, withW, withWWrap, refused)
	if noW < 10000 || withWWrap < 10000 {
		t.Fatalf("the generator covers too little: %d without w, %d wrapping", noW, withWWrap)
	}
}
