package difftest_test

// The log model's claim (harness/rpcmodel/src/log): for the argument kinds and verbs the lab's
// targets log (go-craq's call sites: errors with %v, %#v and %s of Error(), strings, integers,
// pointers to and values of structs of basic fields with %+v, Println of strings), the model calls
// Error()/String() on every argument real fmt calls them on (equal counts under real log, which
// formats with fmt; at least fmt's under the model), and Fatal*/Panic* panic under the model.

import (
	"fmt"
	"log"
	"testing"
)

// logSink is an io.Writer that keeps nothing.
type logSink struct{}

func (*logSink) Write(p []byte) (int, error) { return len(p), nil }

// counted methods
var nErr, nStr int

type cntErr struct{ s string }

func (e *cntErr) Error() string { nErr++; return e.s }

type cntStr struct{ s string }

func (s cntStr) String() string { nStr++; return s.s }

type cntBoth struct{}

func (cntBoth) Error() string  { nErr++; return "both" }
func (cntBoth) String() string { nStr++; return "both" }

// go-craq's logged structs: store.Item (as a pointer) and transport.NodeMeta (a value)
type item struct {
	Version   uint64
	Committed bool
	Value     []byte
	Key       string
}

type meta struct {
	IsHead, IsTail   bool
	Prev, Next, Tail string
}

type logCase struct {
	name   string
	format string
	args   []interface{}
}

func logCases() []logCase {
	e := &cntErr{"boom"}
	return []logCase{
		{"err %v", "Failed to write. %v\n", []interface{}{e}},
		{"err %#v", "Failed during back propagation: %#v\n", []interface{}{e}},
		{"err.Error() %s", "Failed to update successor: %s\n", []interface{}{e.Error()}},
		{"%s %d %#v", "Failed to commit. Key: %s Version: %d Error: %#v", []interface{}{"k0", uint64(3), e}},
		{"item %+v err %#v", "Failed to write item %+v to store: %#v\n", []interface{}{&item{Key: "k"}, e}},
		{"meta %+v", "Received metadata update: %+v\n", []interface{}{meta{Prev: "a"}}},
		{"strings", "connecting to new successor %s\n", []interface{}{"10.77.0.12:7000"}},
		{"%d %s", "Marked version %d of key %s committed.\n", []interface{}{uint64(1), "k1"}},
		{"stringer %v", "x %v\n", []interface{}{cntStr{"s"}}},
		{"error and stringer %v", "x %v\n", []interface{}{cntBoth{}}},
		{"nil error", "x %v\n", []interface{}{nil}},
	}
}

// counts runs f and returns the Error() and String() calls it made.
func counts(f func()) (int, int) {
	nErr, nStr = 0, 0
	f()
	return nErr, nStr
}

func TestLogCallsMethods(t *testing.T) {
	quiet()
	for _, c := range logCases() {
		fe, fs := counts(func() { _ = sprintf(c.format, c.args...) })
		pe, ps := counts(func() { log.Printf(c.format, c.args...) })
		le, ls := counts(func() { log.Default().Printf(c.format, c.args...) })
		ne, ns := counts(func() { log.Println(c.args...) })
		lne, lns := counts(func() { log.Default().Println(c.args...) })
		se, ss := counts(func() { _ = sprintln(c.args...) })
		// a logger of New (as SwiftPaxos's dlog makes one): the model's ignores its writer (not
		// io.Discard: real log formats nothing for that one)
		nw := log.New(&logSink{}, "p ", log.LstdFlags)
		we, ws := counts(func() { nw.Printf(c.format, c.args...) })
		wne, wns := counts(func() { nw.Println(c.args...) })
		for _, r := range []struct {
			what       string
			e, s, w, x int
		}{
			{"Printf", pe, ps, fe, fs}, {"Logger.Printf", le, ls, fe, fs},
			{"Println", ne, ns, se, ss}, {"Logger.Println", lne, lns, se, ss},
			{"New.Printf", we, ws, fe, fs}, {"New.Println", wne, wns, se, ss},
		} {
			if model && (r.e < r.w || r.s < r.x) || !model && (r.e != r.w || r.s != r.x) {
				t.Errorf("%s: %s: Error/String calls %d/%d, fmt's %d/%d", c.name, r.what, r.e, r.s, r.w, r.x)
			}
		}
	}
}

func mustPanic(t *testing.T, what string, f func()) {
	t.Helper()
	defer func() {
		if recover() == nil {
			t.Errorf("%s did not panic", what)
		}
	}()
	f()
}

func TestLogFatalPanics(t *testing.T) {
	if !model {
		t.Skip("real log.Fatal* exit the process")
	}
	e := &cntErr{"boom"}
	for _, f := range []struct {
		what string
		f    func()
	}{
		{"Fatalf", func() { log.Fatalf("x %v", e) }},
		{"Fatalln", func() { log.Fatalln(e) }},
		{"Fatal", func() { log.Fatal(e) }},
		{"Panicf", func() { log.Panicf("x %v", e) }},
		{"Logger.Fatalf", func() { log.Default().Fatalf("x %#v", e) }},
		{"Logger.Panicln", func() { log.Default().Panicln(e) }},
	} {
		n, _ := counts(func() { mustPanic(t, f.what, f.f) })
		if n != 1 {
			t.Errorf("%s: %d Error() calls before the panic, want 1", f.what, n)
		}
	}
}

func TestLogPanicReal(t *testing.T) {
	// real Panic* panic too (the model agrees)
	quiet()
	mustPanic(t, "Panicf", func() { log.Panicf("x %d", 1) })
}

func sprintf(format string, a ...interface{}) string { return fmt.Sprintf(format, a...) }
func sprintln(a ...interface{}) string               { return fmt.Sprintln(a...) }
