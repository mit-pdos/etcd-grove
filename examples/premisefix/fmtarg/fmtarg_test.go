// Package fmtarg checks which method fmt calls on an argument (premise fixes 4, fix 5, 2026-11-10),
// what fmt.argOk (Spec/fmt/Errorf.lean) assumes: for %v/%s fmt calls Format when the type has one
// (in place of Error or String), and Error in place of String when the type is an error; so a
// String method's spec says what fmt does only for a type with neither Format nor Error, and an
// Error method's only for a type without Format. A method fmt calls that panics with a value whose
// Error panics makes Sprintf panic (fmt re-raises a nested panic). Found by the round-2 premise
// attack (fmt-argOk-error-over-string-and-formatter).
//
// Premise fixes 6, D (2026-11-11): which methods fmt calls depends on the verb, what
// Spec/fmt/Errorf.lean's fmt.argsOk (with fmt.fmtDirectives, fmt.argOkAt) assumes. Error()/String()
// only under v s x X q (and w in Errorf); under another verb, or %#v without GoString, the value is
// printed by reflection, which reaches the Format of a nested exported field (the round-3
// counterexample, coord-81 round3 bbolt-cache/fmtverb); a named integer type is printed as an
// integer under %d (raft's ConfChangeType, whose String is not called); arguments left over are
// printed under %v (EXTRA); a * width consumes an argument and %% none. TestDirectives checks
// fmt.fmtDirectives' examples against the verbs Go formats each argument with.
package fmtarg

import (
	"context"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/url"
	"reflect"
	"slices"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/raft/v3/raftpb"
	"golang.org/x/crypto/bcrypt"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
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

// TestNoFormatter: none of the error types the proofs' error predicates describe (http.errStrOk,
// cache's errStrOk, statusErrOk, isEtcdProgressNotifier's error clause; each assumes
// methodSet ei.ty !! "Format" = none) implements fmt.Formatter, so fmt calls their Error method:
// the standard library's errors the proofs see, grpc's *status.Error (from status.Error and from
// status.FromContextError(...).Err()), rpctypes' EtcdError (client side, from rpctypes.Error) and
// the context errors, and bcrypt.GenerateFromPassword's errors.
func TestNoFormatter(t *testing.T) {
	ft := reflect.TypeOf((*fmt.Formatter)(nil)).Elem()
	cctx, cancel := context.WithCancel(context.Background())
	cancel()
	dctx, dcancel := context.WithDeadline(context.Background(), time.Unix(0, 0))
	defer dcancel()
	errs := []error{io.EOF, io.ErrUnexpectedEOF, errors.New("x"), fmt.Errorf("%w", io.EOF),
		&url.Error{}, &net.OpError{}, http.ErrBodyReadAfterClose, http.ErrHandlerTimeout,
		context.Canceled, context.DeadlineExceeded, &net.DNSError{}, &net.AddrError{}, net.ErrClosed,
		status.Error(codes.Unavailable, "m"),
		status.FromContextError(cctx.Err()).Err(),
		status.FromContextError(dctx.Err()).Err(),
		rpctypes.Error(rpctypes.ErrGRPCNoLeader),
		rpctypes.Error(rpctypes.ErrGRPCCompacted),
		rpctypes.ErrNoLeader,
		dctx.Err(),
		// bcrypt.GenerateFromPassword's two errors
		bcrypt.ErrPasswordTooLong, bcrypt.InvalidCostError(99),
	}
	for _, e := range errs {
		if reflect.TypeOf(e).Implements(ft) {
			t.Errorf("%T implements fmt.Formatter", e)
		}
	}
	// the grpc and rpctypes errors are of the types the specs name
	if _, ok := status.Error(codes.Unavailable, "m").(interface{ GRPCStatus() *status.Status }); !ok {
		t.Errorf("status.Error: no GRPCStatus")
	}
	if _, ok := rpctypes.Error(rpctypes.ErrGRPCNoLeader).(rpctypes.EtcdError); !ok {
		t.Errorf("rpctypes.Error(ErrGRPCNoLeader) is %T, not rpctypes.EtcdError", rpctypes.Error(rpctypes.ErrGRPCNoLeader))
	}
	if _, err := bcrypt.GenerateFromPassword(make([]byte, 73), bcrypt.MinCost); err != bcrypt.ErrPasswordTooLong {
		t.Errorf("GenerateFromPassword of 73 bytes: %v", err)
	}
	if _, err := bcrypt.GenerateFromPassword([]byte("p"), 99); reflect.TypeOf(err) != reflect.TypeOf(bcrypt.InvalidCostError(0)) {
		t.Errorf("GenerateFromPassword at cost 99: %T", err)
	}
	if !errors.Is(dctx.Err(), context.DeadlineExceeded) {
		t.Errorf("deadline context's Err is %v", dctx.Err())
	}
}

// calls records the methods fmt calls, in order.
var calls []string

func record(m string) { calls = append(calls, m) }

// called runs f and returns the methods fmt called.
func called(f func()) []string {
	calls = nil
	f()
	return calls
}

// fmtField has a Format method with an effect (recorded).
type fmtField struct{}

func (fmtField) Format(f fmt.State, c rune) { record("Format") }

// errNested is an error without Format whose exported field has a Format (round 3: fmt.argOk
// admitted it under every verb).
type errNested struct{ F fmtField }

func (*errNested) Error() string { record("Error"); return "e" }

// TestVerbRound3: %d of an error calls not its Error() but its nested field's Format, through
// Printf and Errorf; %v calls Error() and not Format.
func TestVerbRound3(t *testing.T) {
	var e error = &errNested{}
	for _, c := range []struct {
		name string
		f    func()
		want []string
	}{
		{"Printf %d", func() { fmt.Printf("%d\n", e) }, []string{"Format"}},
		{"Errorf %d", func() { _ = fmt.Errorf("%d", e) }, []string{"Format"}},
		{"Printf %v", func() { fmt.Printf("%v\n", e) }, []string{"Error"}},
		{"Errorf %v", func() { _ = fmt.Errorf("%v", e) }, []string{"Error"}},
		{"Errorf %w", func() { _ = fmt.Errorf("%w", e) }, []string{"Error"}},
	} {
		if got := called(c.f); !slices.Equal(got, c.want) {
			t.Errorf("%s: called %v, want %v", c.name, got, c.want)
		}
	}
}

// confType is a named int32 with a String method, as raftpb.ConfChangeType.
type confType int32

func (c confType) String() string { record("String"); return "name" }

// TestIntVerb: %d of a named integer type prints the integer without calling String (raft
// confchange's "unexpected conf type %d" of a ConfChangeType); %v calls String.
func TestIntVerb(t *testing.T) {
	var out string
	if got := called(func() { out = fmt.Sprintf("unexpected conf type %d", confType(7)) }); len(got) != 0 || out != "unexpected conf type 7" {
		t.Errorf("%%d of confType: called %v, output %q", got, out)
	}
	if got := called(func() { _ = fmt.Errorf("unexpected conf type %d", confType(7)) }); len(got) != 0 {
		t.Errorf("Errorf %%d of confType: called %v", got)
	}
	if got := called(func() { out = fmt.Sprintf("%v", confType(7)) }); !slices.Equal(got, []string{"String"}) || out != "name" {
		t.Errorf("%%v of confType: called %v, output %q", got, out)
	}
	// the real ConfChangeType: an integer under %d, its name under %v
	if out := fmt.Sprintf("unexpected conf type %d", raftpb.ConfChangeType(7)); out != "unexpected conf type 7" {
		t.Errorf("%%d of raftpb.ConfChangeType(7): %q", out)
	}
	if out := fmt.Sprintf("%d", raftpb.ConfChangeType_ConfChangeRemoveNode); out != "1" {
		t.Errorf("%%d of ConfChangeRemoveNode: %q", out)
	}
	if out := fmt.Sprintf("%v", raftpb.ConfChangeType_ConfChangeRemoveNode); out != "ConfChangeRemoveNode" {
		t.Errorf("%%v of ConfChangeRemoveNode: %q", out)
	}
	if _, ok := any(raftpb.ConfChangeType(0)).(fmt.Formatter); ok {
		t.Errorf("raftpb.ConfChangeType implements fmt.Formatter")
	}
}

// errGo is an error and a Stringer with a GoString method; errNoGo the same without GoString.
type errGo struct{}

func (errGo) Error() string    { record("Error"); return "e" }
func (errGo) String() string   { record("String"); return "s" }
func (errGo) GoString() string { record("GoString"); return "g" }

type errNoGo struct{ F fmtField }

func (*errNoGo) Error() string  { record("Error"); return "e" }
func (*errNoGo) String() string { record("String"); return "s" }

// TestSharpV: %#v calls GoString when the type has one; without it, neither Error nor String,
// and the value is printed by reflection, reaching a nested field's Format.
func TestSharpV(t *testing.T) {
	if got := called(func() { _ = fmt.Sprintf("%#v", errGo{}) }); !slices.Equal(got, []string{"GoString"}) {
		t.Errorf("%%#v with GoString: called %v", got)
	}
	if got := called(func() { _ = fmt.Sprintf("%#v", &errNoGo{}) }); !slices.Equal(got, []string{"Format"}) {
		t.Errorf("%%#v without GoString: called %v, want [Format]", got)
	}
	// %+v is a method verb: Error()
	if got := called(func() { _ = fmt.Sprintf("%+v", &errNoGo{}) }); !slices.Equal(got, []string{"Error"}) {
		t.Errorf("%%+v: called %v", got)
	}
}

// recErr is an error with no field.
type recErr struct{}

func (*recErr) Error() string { record("Error"); return "e" }

// TestMethodVerbs: v s x X q call Error(); d t T p (and w outside Errorf) do not.
func TestMethodVerbs(t *testing.T) {
	e := &recErr{}
	for _, v := range []string{"%v", "%s", "%x", "%X", "%q"} {
		if got := called(func() { _ = fmt.Sprintf(v, e) }); !slices.Equal(got, []string{"Error"}) {
			t.Errorf("%s: called %v, want [Error]", v, got)
		}
	}
	for _, v := range []string{"%d", "%t", "%T", "%p", "%w", "%#v"} {
		if got := called(func() { _ = fmt.Sprintf(v, e) }); len(got) != 0 {
			t.Errorf("%s: called %v, want none", v, got)
		}
	}
	if got := called(func() { _ = fmt.Errorf("%w", e) }); !slices.Equal(got, []string{"Error"}) {
		t.Errorf("Errorf %%w: called %v, want [Error]", got)
	}
}

// TestExtra: arguments left over are printed under %v: Error() of an error, String() of a Stringer.
func TestExtra(t *testing.T) {
	var out string
	if got := called(func() { out = fmt.Sprintf(nonConst("x"), &recErr{}) }); !slices.Equal(got, []string{"Error"}) || out != "x%!(EXTRA *fmtarg.recErr=e)" {
		t.Errorf("EXTRA error: called %v, output %q", got, out)
	}
	if got := called(func() { out = fmt.Sprintf(nonConst("%d"), 1, confType(2)) }); !slices.Equal(got, []string{"String"}) || out != "1%!(EXTRA fmtarg.confType=name)" {
		t.Errorf("EXTRA Stringer: called %v, output %q", got, out)
	}
}

// TestStarAndPercent: a * width consumes an argument, %% none.
func TestStarAndPercent(t *testing.T) {
	if out := fmt.Sprintf("%*d", 5, 3); out != "    3" {
		t.Errorf("%%*d: %q", out)
	}
	if out := fmt.Sprintf("%.*d|%d", 3, 4, 5); out != "004|5" {
		t.Errorf("%%.*d: %q", out)
	}
	if out := fmt.Sprintf("%%d %d", 3); out != "%d 3" {
		t.Errorf("%%%%: %q", out)
	}
	if out := fmt.Sprintf("%5%%d", 3); out != "%3" {
		t.Errorf("%%5%%: %q", out)
	}
	if out := fmt.Sprintf(nonConst("abc%"), 3); out != "abc%!(NOVERB)%!(EXTRA int=3)" {
		t.Errorf("trailing %%: %q", out)
	}
}

// directive is fmt.Directive: a verb and whether it is %#v.
type directive struct {
	verb   rune
	sharpV bool
}

// verbRec records the verb (and the # flag under v) each argument is formatted with.
type verbRec struct {
	i   int
	got *[]directive
	idx *[]int
}

func (r verbRec) Format(f fmt.State, c rune) {
	*r.got = append(*r.got, directive{c, c == 'v' && f.Flag('#')})
	*r.idx = append(*r.idx, r.i)
}

// TestDirectives: for each example of fmt.fmtDirectives (Spec/fmt/Errorf.lean), the verbs Go
// formats the arguments with are the directives, in order, then v for the arguments left over.
func TestDirectives(t *testing.T) {
	for _, c := range []struct {
		format string
		want   []directive
	}{
		{"%w: Limit(%d) not supported", []directive{{'w', false}, {'d', false}}},
		{"%%d %5.2f %#v", []directive{{'f', false}, {'v', true}}},
		{"%#x %+v %-08.3s %.q % d", []directive{{'x', false}, {'v', false}, {'s', false}, {'q', false}, {'d', false}}},
		{"abc%", nil},
		{"%5%%s", []directive{{'s', false}}},
		{"unexpected conf type %d", []directive{{'d', false}}},
	} {
		const n = 7
		var got []directive
		var idx []int
		args := make([]any, n)
		for i := range args {
			args[i] = verbRec{i, &got, &idx}
		}
		_ = fmt.Sprintf(c.format, args...)
		// Sprintf's %w is a bad verb: the argument is printed with no method called (not even
		// Format); the directive still consumes it
		var want []directive
		var wantIdx []int
		for i := 0; i < n; i++ {
			d := directive{'v', false}
			if i < len(c.want) {
				d = c.want[i]
			}
			if d.verb != 'w' {
				want = append(want, d)
				wantIdx = append(wantIdx, i)
			}
		}
		if !slices.Equal(got, want) || !slices.Equal(idx, wantIdx) {
			t.Errorf("%q: verbs %v (arguments %v), want %v", c.format, got, idx, want)
		}
	}
}

// nonConst hides a format from vet (the tests pass formats vet rejects on purpose).
func nonConst(s string) string { return s }
