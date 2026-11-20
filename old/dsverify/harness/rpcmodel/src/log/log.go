// Package log is the dsverify lab's model of Go's log (Go 1.27.3), substituted for the real
// package as net/rpc is (harness/rpcmodel/goroot.sh; notes/craq-net.md, the logging decision).
// Goose translates it in place of the real package for every package of a theorem (the harness's
// and the target's), and the harness proves its specs once (harness/lean/Harness/Proof/log).
//
// The model writes nothing. It keeps the one effect logging can have on safety, running the
// arguments' methods: for each argument that is an error it calls Error(), else, if it is a
// fmt.Stringer, String(), and discards the result. Fatal, Fatalf, Fatalln, Panic, Panicf and
// Panicln do the same, then panic: the real Fatal* exit the process, and the model's panic is the
// lab's choice of a stricter semantics (the proof must show they are unreachable).
//
// The trusted claim (tested against real log and fmt by log_test.go): real log and fmt run no
// code of the program other than those methods. The model calls them at least where real fmt
// does: real fmt calls Error()/String() for the verbs %v, %s, %q, %x, %X and in Print/Println
// (and on exported fields of struct arguments, which go-craq does not log), not for %#v or %d,
// and it recovers a panic in them; the model calls them for every argument and lets a panic
// through. So the model can panic where Go would not, never the reverse.
//
// The subset (what the lab's targets and harness use): Printf, Println, Print, Fatal, Fatalf,
// Fatalln, Panic, Panicf, Panicln, Default, New and the flag constants, Logger and its methods
// of the same names.
package log

// Logger is a logger; the model's has no state.
type Logger struct{}

// stringer is fmt.Stringer (the model does not import fmt).
type stringer interface {
	String() string
}

// touch runs v's formatting method as fmt would: Error() of an error, else String() of a
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

// Default returns a logger (Go's returns the standard logger; the model's loggers are all
// alike).
func Default() *Logger {
	return &Logger{}
}

// The flags of New (Go's values; the model formats nothing, so they have no effect).
const (
	Ldate = 1 << iota
	Ltime
	Lmicroseconds
	Llongfile
	Lshortfile
	LUTC
	Lmsgprefix
	LstdFlags = Ldate | Ltime
)

// New returns a logger. Go's takes out as an io.Writer and writes each line to it; the model's
// writes nothing, so it takes any value (every io.Writer converts to interface{}, so every call
// that compiles against Go's compiles against the model's) and ignores out, prefix and flag.
func New(out interface{}, prefix string, flag int) *Logger {
	return &Logger{}
}

func Printf(format string, v ...interface{}) { touchAll(v) }
func Println(v ...interface{})               { touchAll(v) }
func Print(v ...interface{})                 { touchAll(v) }

func Fatalf(format string, v ...interface{}) { touchAll(v); panic("log.Fatal") }
func Fatalln(v ...interface{})               { touchAll(v); panic("log.Fatal") }
func Fatal(v ...interface{})                 { touchAll(v); panic("log.Fatal") }
func Panicf(format string, v ...interface{}) { touchAll(v); panic("log.Panic") }
func Panicln(v ...interface{})               { touchAll(v); panic("log.Panic") }
func Panic(v ...interface{})                 { touchAll(v); panic("log.Panic") }

func (l *Logger) Printf(format string, v ...interface{}) { touchAll(v) }
func (l *Logger) Println(v ...interface{})               { touchAll(v) }
func (l *Logger) Print(v ...interface{})                 { touchAll(v) }

func (l *Logger) Fatalf(format string, v ...interface{}) { touchAll(v); panic("log.Fatal") }
func (l *Logger) Fatalln(v ...interface{})               { touchAll(v); panic("log.Fatal") }
func (l *Logger) Fatal(v ...interface{})                 { touchAll(v); panic("log.Fatal") }
func (l *Logger) Panicf(format string, v ...interface{}) { touchAll(v); panic("log.Panic") }
func (l *Logger) Panicln(v ...interface{})               { touchAll(v); panic("log.Panic") }
func (l *Logger) Panic(v ...interface{})                 { touchAll(v); panic("log.Panic") }
