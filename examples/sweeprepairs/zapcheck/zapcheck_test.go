package zapcheck

import (
	"testing"

	"go.uber.org/zap"
	"go.uber.org/zap/zapcore"
)

// try reports whether Check(lvl) returns an entry and whether its Write panics.
func try(l *zap.Logger, lvl zapcore.Level) (nonNil, panicked bool) {
	defer func() {
		if r := recover(); r != nil {
			panicked = true
		}
	}()
	ce := l.Check(lvl, "x")
	if ce != nil {
		nonNil = true
		ce.Write()
	}
	return
}

// TestCheck: for every level from Debug (-1) to Fatal-1 and the loggers NewNop, NewNop with
// Development(), and a Development() logger over a no-op core at Debug, Write panics exactly at
// the levels the restricted spec excludes (DPanic with Development, Panic); every level <= Error
// (sint < 3, signed: Debug is W8 255 unsigned) never panics.
func TestCheck(t *testing.T) {
	loggers := map[string]*zap.Logger{
		"NewNop":           zap.NewNop(),
		"NewNop+Dev":       zap.NewNop().WithOptions(zap.Development()),
		"NopCore+Dev+Dbg":  zap.New(zapcore.NewNopCore(), zap.Development()),
	}
	for name, l := range loggers {
		for lvl := zapcore.DebugLevel; lvl <= zapcore.PanicLevel; lvl++ {
			nonNil, panicked := try(l, lvl)
			t.Logf("%s %v (int8 %d): Check non-nil=%v Write panicked=%v", name, lvl, int8(lvl), nonNil, panicked)
			if int8(lvl) < 3 && panicked {
				t.Errorf("%s %v: panicked at a level <= Error", name, lvl)
			}
		}
	}
}
