package difftest_test

// The log/slog model's claim (harness/rpcmodel/src/log/slog): for go-vsr's calls (the package's
// Debug and Info with string, error, Stringer and integer arguments under the default logger; a
// Logger of New(NewTextHandler(w, &HandlerOptions{Level: ...})) with each level; SetDefault),
// the model calls Error()/String() on at least the arguments real slog calls them on; New(nil)
// and a method of a nil *Logger panic in both.

import (
	"log/slog"
	"testing"
)

type slogSink struct{}

func (slogSink) Write(p []byte) (int, error) { return len(p), nil }

func TestSlogCallsMethods(t *testing.T) {
	quiet()
	e := &cntErr{"boom"}
	s := cntStr{"s"}
	args := []interface{}{"err", e, "addr", s, "n", 3, "both", cntBoth{}}
	type call struct {
		what string
		f    func()
	}
	var calls []call
	for _, lv := range []slog.Level{slog.LevelDebug, slog.LevelInfo, slog.LevelWarn, slog.LevelError} {
		l := slog.New(slog.NewTextHandler(slogSink{}, &slog.HandlerOptions{Level: lv}))
		calls = append(calls,
			call{"Logger.Debug", func() { l.Debug("m", args...) }},
			call{"Logger.Info", func() { l.Info("m", args...) }},
			call{"Logger.Warn", func() { l.Warn("m", args...) }},
			call{"Logger.Error", func() { l.Error("m", args...) }},
			call{"Logger.With.Info", func() { l.With("k", e).Info("m", args...) }})
	}
	calls = append(calls,
		call{"Debug", func() { slog.Debug("m", args...) }},
		call{"Info", func() { slog.Info("m", args...) }},
		call{"Warn", func() { slog.Warn("m", args...) }},
		call{"Error", func() { slog.Error("m", args...) }},
		call{"Default.Info", func() { slog.Default().Info("m", args...) }},
		call{"DiscardHandler", func() { slog.New(slog.DiscardHandler).Error("m", args...) }})
	for _, c := range calls {
		ne, ns := counts(c.f)
		// what the handler formats: Error() of e and of cntBoth, String() of s (the model: all
		// of them, for every call; real: those of enabled records)
		if model && (ne < 2 || ns < 1) || ne > 3 || ns > 1 {
			t.Errorf("%s: Error/String calls %d/%d", c.what, ne, ns)
		}
	}
	// SetDefault (cmd/example's), then the package's functions use it
	old := slog.Default()
	slog.SetDefault(slog.New(slog.NewTextHandler(slogSink{}, &slog.HandlerOptions{Level: slog.LevelDebug})))
	if ne, _ := counts(func() { slog.Debug("m", "err", e) }); ne != 1 {
		t.Errorf("Debug after SetDefault at LevelDebug: %d Error calls, want 1", ne)
	}
	slog.SetDefault(old)
}

func TestSlogPanics(t *testing.T) {
	mustPanic(t, "New(nil)", func() { slog.New(nil) })
	var l *slog.Logger
	mustPanic(t, "nil Logger's Info", func() { l.Info("m") })
	mustPanic(t, "nil Logger's Debug", func() { l.Debug("m") })
}
