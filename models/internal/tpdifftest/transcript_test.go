package tpdifftest_test

import (
	"bytes"
	"fmt"
	"os"
	"path/filepath"
	"testing"
)

// outcome runs f: "ok", or "panic: " and the panic's text (a runtime error's message, which the
// model's panics must match), or "panic: NotModelled" for the models' panic value.
func outcome(f func()) (s string) {
	defer func() {
		if r := recover(); r != nil {
			if _, ok := r.(interface{ NotModelled() }); ok {
				s = "panic: NotModelled"
			} else {
				s = fmt.Sprintf("panic: %v", r)
			}
		}
	}()
	f()
	return "ok"
}

// notModelled reports whether f panics with the models' panic value.
func notModelled(f func()) bool { return outcome(f) == "panic: NotModelled" }

// A transcript is what a test observed of a library, line by line: run.sh runs every test against
// the real library and against the model, each writing its transcripts to $TPDIFF_OUT, and
// compares the two directories (they must be byte for byte equal). Without $TPDIFF_OUT the
// transcripts are dropped (the tests' own checks still run).
type transcript struct {
	name string
	buf  bytes.Buffer
	n    int
}

func newTranscript(name string) *transcript { return &transcript{name: name} }

func (t *transcript) printf(format string, args ...interface{}) {
	fmt.Fprintf(&t.buf, format, args...)
	t.buf.WriteByte('\n')
	t.n++
}

func (t *transcript) save(tb testing.TB) {
	tb.Logf("%s: %d transcript lines (model=%v)", t.name, t.n, model)
	dir := os.Getenv("TPDIFF_OUT")
	if dir == "" {
		return
	}
	if err := os.WriteFile(filepath.Join(dir, t.name+".txt"), t.buf.Bytes(), 0o644); err != nil {
		tb.Fatal(err)
	}
}
