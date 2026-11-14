//go:build linux

package semantics

import (
	"testing"
	"time"
)

// TestEmptyWrite (D2: "Go's Write returns fewer bytes than asked only with an
// error"; WriteOutcome's failures all have k < len(bs)). REFUTES D2: a Write
// of no bytes on an end that is not closed and has not shut its write side
// fails, with n = 0 = len(b), in two cases WriteOutcome excludes (it lets an
// empty Write there only succeed, the counterexample
// examples/axiomcx/tcp-emptywrite and notes/axiom-review/tcp-semantics.md):
//
//   - with an expired write deadline: (0, timeout). Go's (*poll.FD).Write
//     checks the deadline (prepareWrite) before any write(2);
//   - after the peer's RST: (0, ECONNRESET) if no call took the error yet,
//     then (0, EPIPE), and (0, EPIPE) after a Read took ECONNRESET. Go calls
//     write(2) even for an empty buffer, and Linux's tcp_sendmsg_locked
//     checks the socket's error and state (sk_stream_wait_connect in CLOSE)
//     before it looks at the length.
//
// On a live connection an empty Write is (0, nil), and after CloseWrite
// (0, EPIPE) (allowed: the direction is fin).
func TestEmptyWrite(t *testing.T) {
	t.Parallel()
	d, _ := pair(t)
	if n, err := d.Write(nil); n != 0 || err != nil {
		t.Fatalf("empty Write, live = %d, %v; want 0, nil", n, err)
	}
	d.SetWriteDeadline(time.Now())
	if n, err := d.Write(nil); n != 0 || name(err) != "timeout" {
		t.Fatalf("empty Write, expired deadline = %d, %v; want 0, timeout", n, err)
	}
	d.SetWriteDeadline(time.Time{})
	if n, err := d.Write(nil); n != 0 || err != nil {
		t.Fatalf("empty Write, deadline cleared = %d, %v; want 0, nil", n, err)
	}
	if err := d.CloseWrite(); err != nil {
		t.Fatal(err)
	}
	if n, err := d.Write(nil); n != 0 || name(err) != "EPIPE" {
		t.Fatalf("empty Write after CloseWrite = %d, %v; want 0, EPIPE", n, err)
	}

	c, peer := pair(t)
	resetBy(t, c, peer)
	if n, err := c.Write(nil); n != 0 || name(err) != "ECONNRESET" {
		t.Fatalf("empty Write after RST = %d, %v; want 0, ECONNRESET", n, err)
	}
	if n, err := c.Write(nil); n != 0 || name(err) != "EPIPE" {
		t.Fatalf("second empty Write after RST = %d, %v; want 0, EPIPE", n, err)
	}

	c2, peer2 := pair(t)
	resetBy(t, c2, peer2)
	if got := readSeq(t, c2, 1); got != "ECONNRESET" {
		t.Fatalf("Read after RST = %q; want ECONNRESET", got)
	}
	if n, err := c2.Write(nil); n != 0 || name(err) != "EPIPE" {
		t.Fatalf("empty Write after RST and Read = %d, %v; want 0, EPIPE", n, err)
	}
}
