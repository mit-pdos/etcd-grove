package slogdifftest

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"sync"
	"sync/atomic"
	"testing"
)

// A transcript is what a test observed of log/slog, line by line: run.sh runs the tests against
// Go's log/slog and against the model, each writing its transcripts to $SLOGDIFF_OUT, and the two
// must be byte for byte equal.
type transcript struct {
	name string
	buf  bytes.Buffer
}

func (t *transcript) printf(format string, args ...any) {
	fmt.Fprintf(&t.buf, format, args...)
	t.buf.WriteByte('\n')
}

func (t *transcript) save(tb testing.TB) {
	if dir := os.Getenv("SLOGDIFF_OUT"); dir != "" {
		if err := os.WriteFile(filepath.Join(dir, t.name+".txt"), t.buf.Bytes(), 0o644); err != nil {
			tb.Fatal(err)
		}
	}
}

// outcome runs f: "ok", or the panic: "panic runtime.Error" for a runtime error (the transcript
// does not compare their texts), else "panic <value>".
func outcome(f func()) (s string) {
	defer func() {
		if r := recover(); r != nil {
			if _, ok := r.(runtime.Error); ok {
				s = "panic runtime.Error"
			} else {
				s = fmt.Sprintf("panic %v", r)
			}
		}
	}()
	f()
	return "ok"
}

// spy counts the calls of the methods slog may call on an argument to format it.
var spyCalls atomic.Int64

type spy struct{ n int }

func (s spy) String() string                      { spyCalls.Add(1); return "spy" }
func (s spy) Error() string                       { spyCalls.Add(1); return "spy" }
func (s spy) MarshalText() ([]byte, error)        { spyCalls.Add(1); return []byte("spy"), nil }
func (s spy) Format(f fmt.State, verb rune)       { spyCalls.Add(1) }
func (s spy) MarshalJSON() ([]byte, error)        { spyCalls.Add(1); return []byte(`"spy"`), nil }
func (s *spy) Write(p []byte) (int, error)        { spyCalls.Add(1); return len(p), nil }
func (s spy) GoString() string                    { spyCalls.Add(1); return "spy" }
func (s spy) Unwrap() error                       { spyCalls.Add(1); return nil }
func (s spy) Is(error) bool                       { spyCalls.Add(1); return false }
func (s spy) As(any) bool                         { spyCalls.Add(1); return false }
func (s spy) Value() any                          { spyCalls.Add(1); return nil }
func (s spy) Kind() string                        { spyCalls.Add(1); return "" }
func (s spy) Ctx(context.Context) context.Context { spyCalls.Add(1); return nil }

// argLists are the arguments the tests log with: none, keys and values, an odd count (Go's
// !BADKEY), values with every method slog might call, nils, a panicking String's owner.
func argLists() [][]any {
	var nilErr error
	var nilPtr *spy
	return [][]any{
		nil,
		{"k"},
		{"k", 1},
		{"k", 1, "j"},
		{"k", "v", "n", 42, "f", 1.5, "b", true},
		{"spy", spy{1}, "err", error(spy{2}), "ptr", &spy{3}},
		{spy{4}},
		{"nil", nil, "nilerr", nilErr, "nilptr", nilPtr},
		{"err", errors.New("boom"), "wrapped", fmt.Errorf("w: %w", spy{5})},
		{1, 2, 3},
	}
}

type logFn struct {
	name string
	f    func(msg string, args ...any)
}

func methods(l *slog.Logger) []logFn {
	return []logFn{{"Debug", l.Debug}, {"Info", l.Info}, {"Warn", l.Warn}, {"Error", l.Error}}
}

// TestDiscard: a Logger over DiscardHandler: every call returns, no argument method is called.
func TestDiscard(t *testing.T) {
	tr := &transcript{name: "discard"}
	lists := argLists() // (building them formats one: fmt.Errorf)
	spyCalls.Store(0)
	l := slog.New(slog.DiscardHandler)
	for _, m := range methods(l) {
		for i, args := range lists {
			tr.printf("%s args#%d: %s", m.name, i, outcome(func() { m.f("msg", args...) }))
		}
	}
	tr.printf("argument methods called: %d", spyCalls.Load())
	if spyCalls.Load() != 0 {
		t.Errorf("argument methods called %d times", spyCalls.Load())
	}
	// DiscardHandler's own methods (Go's code in both)
	h := slog.DiscardHandler
	for _, lv := range []slog.Level{slog.LevelDebug, slog.LevelInfo, slog.LevelWarn, slog.LevelError, -100, 100} {
		tr.printf("DiscardHandler.Enabled(%d) = %v", int(lv), h.Enabled(context.Background(), lv))
	}
	tr.printf("Handle = %v", h.Handle(context.Background(), slog.Record{}))
	tr.printf("WithAttrs is DiscardHandler: %v", h.WithAttrs(nil) == slog.DiscardHandler)
	tr.printf("WithGroup is DiscardHandler: %v", h.WithGroup("g") == slog.DiscardHandler)
	tr.printf("New(DiscardHandler.WithGroup(g)).Info: %s",
		outcome(func() { slog.New(h.WithGroup("g")).Info("m", "k", spy{}) }))
	tr.printf("constants %d %d %d %d", slog.LevelDebug, slog.LevelInfo, slog.LevelWarn, slog.LevelError)
	tr.save(t)
}

// TestDefaultDebug: the package-level Debug (the default logger, level Info): returns, no
// argument method is called.
func TestDefaultDebug(t *testing.T) {
	tr := &transcript{name: "default-debug"}
	lists := argLists()
	spyCalls.Store(0)
	for i, args := range lists {
		tr.printf("Debug args#%d: %s", i, outcome(func() { slog.Debug("msg", args...) }))
	}
	tr.printf("argument methods called: %d", spyCalls.Load())
	if spyCalls.Load() != 0 {
		t.Errorf("argument methods called %d times", spyCalls.Load())
	}
	tr.save(t)
}

// TestNil: a nil *Logger's methods panic (a nil dereference); New(nil) panics with "nil Handler".
func TestNil(t *testing.T) {
	tr := &transcript{name: "nil"}
	var l *slog.Logger
	for _, m := range methods(l) {
		for i, args := range argLists()[:3] {
			tr.printf("nil %s args#%d: %s", m.name, i, outcome(func() { m.f("msg", args...) }))
		}
	}
	tr.printf("nil Handler(): %s", outcome(func() { l.Handler() }))
	tr.printf("New(nil): %s", outcome(func() { slog.New(nil) }))
	tr.printf("New(nil Handler var): %s", outcome(func() { var h slog.Handler; slog.New(h) }))
	tr.save(t)
}

// TestHandler: Logger.Handler returns the Logger's handler (Go's code in both): its identity, its
// type, its methods; a zero Logger's is nil.
func TestHandler(t *testing.T) {
	tr := &transcript{name: "handler"}
	l := slog.New(slog.DiscardHandler)
	h := l.Handler()
	tr.printf("Handler() == DiscardHandler: %v; %%T %T; %%v %v; %%#v %#v", h == slog.DiscardHandler, h, h, h)
	tr.printf("Enabled(Error) %v; Handle %v; WithAttrs == DiscardHandler %v; WithGroup %v",
		h.Enabled(context.Background(), slog.LevelError), h.Handle(context.Background(), slog.Record{}),
		h.WithAttrs(nil) == slog.DiscardHandler, h.WithGroup("g") == slog.DiscardHandler)
	tr.printf("New(Handler()) Info: %s", outcome(func() { slog.New(h).Info("m", "k", spy{}) }))
	_, isWG := h.(interface{ WithGroup(string) slog.Handler })
	tr.printf("type assertion WithGroup: %v", isWG)
	var z slog.Logger
	tr.printf("zero Logger: Handler() == nil %v", z.Handler() == nil)
	for _, m := range methods(&z) {
		tr.printf("zero Logger %s: %s", m.name, outcome(func() { m.f("msg", "k", 1) }))
	}
	tr.printf("zero Logger %%v %v; New(DiscardHandler) %%v %v %%+v %+v", z, *l, *l)
	tr.save(t)
}

// TestLevel: Level's methods (Go's code in both): String, fmt, JSON and text, parsing.
func TestLevel(t *testing.T) {
	tr := &transcript{name: "level"}
	for lv := slog.Level(-12); lv <= 14; lv++ {
		j, jerr := lv.MarshalJSON()
		x, xerr := lv.MarshalText()
		a, aerr := lv.AppendText([]byte("p:"))
		js, _ := json.Marshal(struct{ L slog.Level }{lv})
		tr.printf("%d: String %s; %%v %v; %%d %d; json %s %v; text %s %v; append %s %v; struct %s; Level %d",
			int(lv), lv.String(), lv, lv, j, jerr, x, xerr, a, aerr, js, int(lv.Level()))
	}
	for _, in := range []string{"DEBUG", "debug", "Info", "WARN", "ERROR", "error+2", "INFO-3",
		"WARN+0", "ERROR-10", "INFO+", "INFO+x", "FATAL", "", "DEBUG+99999999999999999999", "warn-4",
		"4", "INFO +1"} {
		var a, b slog.Level
		ea := a.UnmarshalText([]byte(in))
		eb := b.UnmarshalJSON([]byte(fmt.Sprintf("%q", in)))
		var c slog.Level
		ec := c.UnmarshalJSON([]byte(in))
		tr.printf("%q: text %d %v; json %d %v; raw json %d %v", in, int(a), ea, int(b), eb, int(c), ec)
	}
	var st struct{ L slog.Level }
	err := json.Unmarshal([]byte(`{"L":"WARN+1"}`), &st)
	tr.printf("struct unmarshal %d %v", int(st.L), err)
	tr.save(t)
}

type progHandler struct{ calls *int }

func (h progHandler) Enabled(context.Context, slog.Level) bool  { *h.calls++; return true }
func (h progHandler) Handle(context.Context, slog.Record) error { *h.calls++; return nil }
func (h progHandler) WithAttrs([]slog.Attr) slog.Handler        { return h }
func (h progHandler) WithGroup(string) slog.Handler             { return h }

// TestProgramHandler: a Handler the program supplies is outside the model (a NotModelled panic at
// New in the model; Go's calls it), here also one obtained by wrapping DiscardHandler.
func TestProgramHandler(t *testing.T) {
	n := 0
	r := notModelledPanic(func() { slog.New(progHandler{&n}).Info("m") })
	if model && !r {
		t.Errorf("model: New(program handler) did not panic NotModelled")
	}
	if !model && (r || n != 2) {
		t.Errorf("Go: panicked %v, handler calls %d", r, n)
	}
	type wrapped struct{ slog.Handler }
	r = notModelledPanic(func() { slog.New(wrapped{slog.DiscardHandler}).Info("m") })
	if model != r {
		t.Errorf("wrapped DiscardHandler: NotModelled %v (model %v)", r, model)
	}
}

func notModelledPanic(f func()) (nm bool) {
	defer func() {
		r := recover()
		_, nm = r.(interface{ NotModelled() })
	}()
	f()
	return false
}

// TestConcurrent: calls from many goroutines at once return.
func TestConcurrent(t *testing.T) {
	tr := &transcript{name: "concurrent"}
	spyCalls.Store(0)
	l := slog.New(slog.DiscardHandler)
	var wg sync.WaitGroup
	for g := 0; g < 16; g++ {
		wg.Add(1)
		go func(g int) {
			defer wg.Done()
			for i := 0; i < 1000; i++ {
				l.Error("m", "g", g, "i", i, "spy", spy{})
				slog.Debug("m", "g", g, "spy", spy{})
			}
		}(g)
	}
	wg.Wait()
	tr.printf("done; argument methods called: %d", spyCalls.Load())
	tr.save(t)
}

// TestNoOutput: a child process making every call above writes nothing to stdout or stderr
// (but the test framework's PASS).
func TestNoOutput(t *testing.T) {
	if os.Getenv("SLOGDIFF_CHILD") != "" {
		l := slog.New(slog.DiscardHandler)
		for _, m := range methods(l) {
			for _, args := range argLists() {
				m.f("msg", args...)
			}
		}
		for _, args := range argLists() {
			slog.Debug("msg", args...)
		}
		return
	}
	tr := &transcript{name: "no-output"}
	exe, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(exe, "-test.run=^TestNoOutput$", "-test.count=1")
	cmd.Env = append(os.Environ(), "SLOGDIFF_CHILD=1")
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	if err := cmd.Run(); err != nil {
		t.Fatalf("child: %v\n%s%s", err, stdout.String(), stderr.String())
	}
	tr.printf("stdout %q stderr %q", stdout.String(), stderr.String())
	if stdout.String() != "PASS\n" || stderr.Len() != 0 {
		t.Errorf("child wrote stdout %q stderr %q", stdout.String(), stderr.String())
	}
	tr.save(t)
}
