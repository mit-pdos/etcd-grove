// Package slog is the dsverify lab's model of Go's log/slog (Go 1.27.3), substituted for the real
// package as log is (harness/rpcmodel/goroot.sh; notes/vsr-net.md). Goose translates it in place
// of the real package for every package of a theorem, and the harness proves its specs once
// (harness/lean/Harness/Proof/log/slog.lean).
//
// The model writes nothing. As the log model, it keeps the effects logging can have on safety:
// for each argument that is an error it calls Error(), else, if it is a fmt.Stringer, String(),
// and discards the result; and a method called on a nil *Logger panics (Go's dereferences it).
// New panics on a nil handler, as Go's does.
//
// The trusted claim (tested against real log/slog by rpcmodel/difftest/slog_test.go): real
// log/slog runs no code of the program other than those methods, for the program's handlers and
// levels. Real slog calls them only when the record is enabled and its handler formats the
// argument (a TextHandler or JSONHandler calls Error(), String(), and also LogValue() of a
// LogValuer and MarshalText()/MarshalJSON() of an argument that has them, which the model does
// not call: arguments with such methods are outside the model; the default logger and
// DiscardHandler call nothing for a disabled level); the model calls Error()/String() for every
// argument, enabled or not. So the model may call a method Go would not, never the reverse
// (within the subset), and its panics are a superset of Go's.
//
// The subset (what go-vsr uses): Logger, New, Default, (*Logger).Debug, Info, Warn, Error,
// With; the package's Debug, Info, Warn, Error, SetDefault; Handler, DiscardHandler, HandlerOptions, Level
// and its constants, NewTextHandler (the model's handlers are opaque values).
package slog

// stringer is fmt.Stringer (the model does not import fmt).
type stringer interface {
	String() string
}

// touch runs v's formatting method as a handler would: Error() of an error, else String() of a
// Stringer.
func touch(v interface{}) {
	if e, ok := v.(error); ok {
		_ = e.Error()
		return
	}
	if s, ok := v.(stringer); ok {
		_ = s.String()
	}
}

func touchAll(vs []interface{}) {
	for _, v := range vs {
		touch(v)
	}
}

// Handler is a log handler. The model's handlers write nothing; Go's is an interface with
// Enabled, Handle, WithAttrs and WithGroup, which the model does not call.
type Handler interface{}

// discardHandler is the model's DiscardHandler.
type discardHandler struct{}

// DiscardHandler discards all log output (Go's: a handler whose Enabled is false).
var DiscardHandler Handler = discardHandler{}

// Level is a log level (Go's values).
type Level int

const (
	LevelDebug Level = -4
	LevelInfo  Level = 0
	LevelWarn  Level = 4
	LevelError Level = 8
)

// HandlerOptions are a handler's options; the model keeps none.
type HandlerOptions struct {
	AddSource bool
	Level     interface{}
}

// textHandler is the model's TextHandler.
type textHandler struct{}

// NewTextHandler returns a handler (Go's writes text lines to w; the model's writes nothing, so
// it takes any value as w, as the log model's New does).
func NewTextHandler(w interface{}, opts *HandlerOptions) Handler {
	return textHandler{}
}

// A Logger logs records; the model's holds its handler, which it never calls.
type Logger struct {
	handler Handler
}

// New returns a logger with handler h; it panics if h is nil (Go's).
func New(h Handler) *Logger {
	if h == nil {
		panic("nil Handler")
	}
	return &Logger{handler: h}
}

// Default returns a logger (Go's returns the default logger, whose default handler writes Info
// and above through log; the model's loggers are all alike).
func Default() *Logger {
	return &Logger{handler: discardHandler{}}
}

// handlerOf reads l's handler: a nil l panics, as Go's methods do (they read l.handler).
func (l *Logger) handlerOf() Handler {
	return l.handler
}

// With returns a logger with the same handler (Go's adds the arguments as attributes; the
// model touches them).
func (l *Logger) With(args ...interface{}) *Logger {
	h := l.handlerOf()
	touchAll(args)
	return &Logger{handler: h}
}

func (l *Logger) Debug(msg string, args ...interface{}) { l.handlerOf(); touchAll(args) }
func (l *Logger) Info(msg string, args ...interface{})  { l.handlerOf(); touchAll(args) }
func (l *Logger) Warn(msg string, args ...interface{})  { l.handlerOf(); touchAll(args) }
func (l *Logger) Error(msg string, args ...interface{}) { l.handlerOf(); touchAll(args) }

// SetDefault makes l the default logger (Go's; the model's package functions do not depend on it:
// they behave as every model logger does). A nil l panics, as Go's.
func SetDefault(l *Logger) {
	l.handlerOf()
}

func Debug(msg string, args ...interface{}) { touchAll(args) }
func Info(msg string, args ...interface{})  { touchAll(args) }
func Warn(msg string, args ...interface{})  { touchAll(args) }
func Error(msg string, args ...interface{}) { touchAll(args) }

// Attr is a key-value pair (Go's has a Value of its own type). No function of the model takes or
// returns one: the type is here so that go vet's slog check, which looks it up, runs on programs
// built with the model.
type Attr struct {
	Key string
}
