//go:build linux

package semantics

import (
	"bytes"
	"errors"
	"io"
	"net"
	"os"
	"testing"
	"time"
)

// TestReadDeadlineLosesNothing (D1: "with rdl: a timeout error, nothing
// changes (no byte lost)"; D5). A Read under a deadline that passes returns
// a timeout (errors.Is(err, os.ErrDeadlineExceeded), net.Error.Timeout()).
// While the deadline is expired, a Read returns the timeout at once even
// with bytes arrived, and consumes none (Go's prepareRead checks the
// deadline before read(2)). After SetReadDeadline(time.Time{}) the
// connection reads them, in order. Supports D1, D5.
func TestReadDeadlineLosesNothing(t *testing.T) {
	t.Parallel()
	w, r := pair(t)
	r.SetReadDeadline(time.Now().Add(20 * time.Millisecond))
	_, err := r.Read(make([]byte, 4))
	var ne net.Error
	if !errors.Is(err, os.ErrDeadlineExceeded) || !errors.As(err, &ne) || !ne.Timeout() {
		t.Fatalf("Read past its deadline: %v; want a timeout", err)
	}
	mustWrite(t, w, "abc")
	waitInq(t, r, 3)
	if n, err := r.Read(make([]byte, 4)); n != 0 || name(err) != "timeout" || inq(t, r) != 3 {
		t.Fatalf("Read with expired deadline, bytes arrived = %d, %v (%d left); want 0, timeout, 3 left", n, err, inq(t, r))
	}
	if err := r.SetReadDeadline(time.Time{}); err != nil {
		t.Fatal(err)
	}
	if got := readSeq(t, r, 1); got != "data:abc" {
		t.Fatalf("Read after clearing the deadline = %q; want data:abc", got)
	}
}

// TestWriteDeadlinePrefix (D2: "with wdl: a prefix appended, timeout error, d
// stays open"; D5). A writes 64 MiB under a 100 ms write deadline to B,
// which does not read: the Write returns 0 < n < len and a timeout. Exactly
// those n bytes reach B: after the deadline is cleared, A writes "END" and
// CloseWrites, and B reads n bytes of the buffer then "END" then EOF.
// Supports D2 (the prefix counted by n is the prefix appended; d stays open).
func TestWriteDeadlinePrefix(t *testing.T) {
	t.Parallel()
	a, b := pair(t)
	const size = 64 << 20
	data := make([]byte, size)
	for i := range data {
		data[i] = byte(i * 7)
	}
	a.SetWriteDeadline(time.Now().Add(100 * time.Millisecond))
	n, err := a.Write(data)
	t.Logf("write under deadline: n = %d of %d, err = %v", n, size, err)
	if n <= 0 || n >= size || name(err) != "timeout" {
		t.Fatalf("Write past its deadline = %d, %v; want 0 < n < %d, timeout", n, err, size)
	}
	if err := a.SetWriteDeadline(time.Time{}); err != nil {
		t.Fatal(err)
	}
	done := make(chan error, 1)
	go func() {
		_, err := a.Write([]byte("END"))
		if err == nil {
			err = a.CloseWrite()
		}
		done <- err
	}()
	b.SetReadDeadline(time.Now().Add(30 * time.Second))
	got, err := io.ReadAll(b)
	if err != nil {
		t.Fatalf("B's ReadAll: %v", err)
	}
	if err := <-done; err != nil {
		t.Fatalf("A's Write after clearing the deadline: %v", err)
	}
	want := append(append([]byte{}, data[:n]...), "END"...)
	if !bytes.Equal(got, want) {
		t.Fatalf("B read %d bytes; want the %d-byte prefix then END (%d)", len(got), n, len(want))
	}
}
