//go:build linux

package semantics

import (
	"errors"
	"io"
	"net"
	"testing"
	"time"
)

// TestReadPartial (D1, ReadStep: "bytes unread: returns some k, 1 <= k <=
// min(n, unread), the first k, removed"). A Read returns what has arrived,
// without waiting for its buffer to fill, and a Read smaller than what has
// arrived leaves the rest, in order. Measured: k = min(n, unread) on
// loopback; the decision allows any k >= 1, which Linux also takes in
// general (segments arriving between two reads; read(2): "may be less").
// Supports D1.
func TestReadPartial(t *testing.T) {
	t.Parallel()
	w, r := pair(t)
	mustWrite(t, w, "abc")
	waitInq(t, r, 3)
	buf := make([]byte, 10)
	r.SetReadDeadline(time.Now().Add(guard))
	n, err := r.Read(buf)
	if err != nil || string(buf[:n]) != "abc" {
		t.Fatalf("Read(10) with 3 arrived = %q, %v; want \"abc\", nil (no wait for more)", buf[:n], err)
	}
	mustWrite(t, w, "defgh")
	waitInq(t, r, 5)
	n, err = r.Read(buf[:2])
	if err != nil || string(buf[:n]) != "de" {
		t.Fatalf("Read(2) with 5 arrived = %q, %v; want \"de\"", buf[:n], err)
	}
	if got := inq(t, r); got != 3 {
		t.Fatalf("after Read(2): %d unread, want 3 (the rest stays)", got)
	}
	n, err = r.Read(buf)
	if err != nil || string(buf[:n]) != "fgh" {
		t.Fatalf("Read(10) = %q, %v; want \"fgh\"", buf[:n], err)
	}
}

// TestReadEmptyBuffer (D1, ReadStep: "closed end: error"; "n = 0: returns 0,
// nil at once"). Go's poll.FD.Read returns 0, nil for an empty buffer before
// touching the socket (no read(2) call) and after taking the fd's read lock,
// so: 0, nil without waiting (nothing arrived), without consuming (bytes
// arrived), with an expired read deadline, and after the peer's RST (the
// pending error is not consumed: the next non-empty Read still gets it); but
// ErrClosed after the end's own Close. Supports D1, in its clause order
// (closed first, then n = 0, before the deadline).
func TestReadEmptyBuffer(t *testing.T) {
	t.Parallel()
	w, r := pair(t)
	if n, err := r.Read(nil); n != 0 || err != nil {
		t.Fatalf("Read(empty), nothing arrived = %d, %v; want 0, nil", n, err)
	}
	mustWrite(t, w, "xy")
	waitInq(t, r, 2)
	if n, err := r.Read([]byte{}); n != 0 || err != nil || inq(t, r) != 2 {
		t.Fatalf("Read(empty), 2 arrived = %d, %v, %d left; want 0, nil, 2", n, err, inq(t, r))
	}
	r.SetReadDeadline(time.Now().Add(-time.Second))
	if n, err := r.Read([]byte{}); n != 0 || err != nil {
		t.Fatalf("Read(empty), expired deadline = %d, %v; want 0, nil", n, err)
	}
	r.SetReadDeadline(time.Time{})
	resetBy(t, r, w) // w closes with r's byte unread: RST to r
	if n, err := r.Read([]byte{}); n != 0 || err != nil {
		t.Fatalf("Read(empty) after RST = %d, %v; want 0, nil", n, err)
	}
	if got := readSeq(t, r, 4); got != "data:xy ECONNRESET EOF" {
		t.Fatalf("reads after RST = %q; want the RST still pending after the empty read", got)
	}
	r.Close()
	if n, err := r.Read([]byte{}); n != 0 || !errors.Is(err, net.ErrClosed) {
		t.Fatalf("Read(empty) after own Close = %d, %v; want ErrClosed", n, err)
	}
}

// TestReadEOFAfterFin (D1: "no bytes, d is fin: EOF", nothing changes; D3:
// Close of an end with no unread input sends FIN). The peer writes, then
// Closes: the reader gets every byte, then EOF, and EOF again on every later
// Read. Supports D1, D3.
func TestReadEOFAfterFin(t *testing.T) {
	t.Parallel()
	w, r := pair(t)
	mustWrite(t, w, "xyz")
	if err := w.Close(); err != nil {
		t.Fatalf("Close: %v", err)
	}
	waitState(t, r, tcpCloseWait)
	if got := readSeq(t, r, 4); got != "data:xyz EOF" {
		t.Fatalf("reads = %q; want data:xyz EOF", got)
	}
	for i := 0; i < 3; i++ {
		if n, err := r.Read(make([]byte, 8)); n != 0 || err != io.EOF {
			t.Fatalf("Read after EOF = %d, %v; want 0, EOF again", n, err)
		}
	}
}
