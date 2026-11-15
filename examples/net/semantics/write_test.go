//go:build linux

package semantics

import (
	"errors"
	"io"
	"net"
	"os"
	"testing"
	"time"
)

// TestEmptyWrite (D2: an empty Write is one step, which may fail; allowed
// since v2.1). It REFUTED v2's D2 ("Go's Write returns fewer bytes than asked
// only with an error"; WriteOutcome's failures all had k < len(bs)): a Write
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

// TestWriteDeadlineSetDuring (D2, D15; the v3 review's R1, which refuted v3's
// one-step Write: notes/axiom-review/tcp-semantics.md, the counterexample
// examples/axiomcx/tcp-writedeadline, whose test this is). A Write of 32 MiB
// blocks; the peer reads one byte; another goroutine then sets the writer's
// deadline (to now; or to 100 ms from now, which expires while the Write
// blocks); the Write returns (n, err) with 0 < n < len and err an *OpError
// whose Err is os.ErrDeadlineExceeded itself, Timeout() true; the peer then
// reads exactly n bytes (the first one included) before the writer's Close
// makes it read EOF. Go's (*poll.FD).Write (internal/poll/fd_unix.go) checks
// the deadline in each waitWrite of its loop, and SetDeadline re-arms the
// poller's timer and wakes a waiter whose deadline passed
// (runtime_pollSetDeadline). In the model (v3.1) the Write's steps before the
// SetDeadline append bytes and its step after it times out. Measured.
func TestWriteDeadlineSetDuring(t *testing.T) {
	t.Parallel()
	const size = 32 << 20 // more than loopback's socket buffers hold
	for _, mode := range []string{"now", "future"} {
		c, a := pair(t)
		read1 := make(chan error)
		go func() {
			b := make([]byte, 1)
			_, err := a.Read(b)
			switch mode {
			case "now":
				c.SetDeadline(time.Now())
			case "future":
				c.SetWriteDeadline(time.Now().Add(100 * time.Millisecond))
			}
			read1 <- err
		}()
		n, err := c.Write(make([]byte, size))
		if err1 := <-read1; err1 != nil {
			t.Errorf("%s: first Read: %v", mode, err1)
		}
		var oe *net.OpError
		if !errors.As(err, &oe) || oe.Err != os.ErrDeadlineExceeded || !oe.Timeout() {
			t.Fatalf("%s: Write = (%d, %v); want a deadline error", mode, n, err)
		}
		if n <= 0 || n >= size {
			t.Errorf("%s: Write wrote %d of %d bytes; want 0 < n < size", mode, n, size)
		}
		c.Close()
		a.SetReadDeadline(time.Now().Add(10 * guard))
		r, cerr := io.Copy(io.Discard, a)
		if cerr != nil {
			t.Errorf("%s: Copy: %v", mode, cerr)
		}
		if 1+r != int64(n) {
			t.Errorf("%s: the peer read %d bytes; the Write returned %d", mode, 1+r, n)
		}
	}
}
