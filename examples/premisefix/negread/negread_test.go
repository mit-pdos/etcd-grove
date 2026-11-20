// Package negread checks that io.ReadAll panics on a reader whose Read returns a negative count
// (prove-http, 2026-11-20): http.prefixReaderOk (Proof/net/http/Boundary.lean) related the count
// n to the bytes read by ys.length = sint.nat n, which a Read returning (-1, nil) met (sint.nat of a
// negative is 0), so http.ReadAll_spec proved that io.ReadAll of such a reader returns. Go's
// io.ReadAll slices b[:len(b)+n] (io.go:723) and panics. The fix: sint.Z n = ys.length.
package negread

import (
	"io"
	"strings"
	"testing"
)

type negReader struct{}

func (negReader) Read(p []byte) (int, error) { return -1, nil }

func TestReadAllNegativeCountPanics(t *testing.T) {
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("io.ReadAll of a reader returning -1 did not panic")
		}
		if !strings.Contains(r.(error).Error(), "slice bounds out of range") {
			t.Fatalf("unexpected panic: %v", r)
		}
	}()
	io.ReadAll(negReader{})
}
