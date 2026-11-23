//go:build linux

package semantics

import (
	"net"
	"strings"
	"testing"
	"time"
)

// Sticky read errors (notes/net-sticky-read.md; D1, D14). Which errors a Read
// returns are final: after one, does every later non-empty Read of the end
// return no byte, with an error? Linux's tcp_recvmsg_locked copies queued data
// before it looks at the socket's state, and returns an error (sock_error of
// sk_err) or 0 (EOF: SOCK_DONE or RCV_SHUTDOWN) only when it copied nothing,
// so an error comes only once nothing is unread; and every way a connected
// socket gets an error (tcp_reset, tcp_write_err) or EOF (tcp_fin) also ends
// its receiving (tcp_done: sk_shutdown = SHUTDOWN_MASK; tcp_fin: RCV_SHUTDOWN),
// so no byte arrives after it. Each test reads on past the first error and
// records the unread count (SIOCINQ) when it came. Read-deadline timeouts are
// the exception (TestStickyNotTimeout): Go's own check, before read(2), which
// changes nothing in the kernel.

// stickyReads reads (64-byte buffers, each bounded by guard) until the first
// error (at most 8 Reads), records the unread count then, and makes `after`
// more Reads. It returns what each Read returned ("data:<bytes>" or the
// error's name) and the unread count at the first error.
func stickyReads(t *testing.T, c *net.TCPConn, after int) (string, int) {
	t.Helper()
	var out []string
	one := func() error {
		c.SetReadDeadline(time.Now().Add(guard))
		buf := make([]byte, 64)
		n, err := c.Read(buf)
		if n > 0 {
			out = append(out, "data:"+string(buf[:n]))
		}
		if err != nil {
			out = append(out, name(err))
		}
		return err
	}
	atErr := -1
	for i := 0; i < 8; i++ {
		if err := one(); err != nil {
			atErr = inq(t, c)
			break
		}
	}
	if atErr < 0 {
		t.Fatalf("no Read error in 8 Reads: %s", strings.Join(out, " "))
	}
	for i := 0; i < after; i++ {
		one()
	}
	c.SetReadDeadline(time.Time{})
	return strings.Join(out, " "), atErr
}

// wres is a Write's count and error name.
func wres(c net.Conn, s string) string {
	n, err := c.Write([]byte(s))
	return itoa(n) + "," + name(err)
}

// TestStickyEOF (D1: EOF once nothing is unread and the writer is done; the
// proposed sticky rule). W writes "xyz" and CloseWrites (FIN); R reads the
// bytes, then EOF, and EOF on every later Read. Then R Writes "late" (its own
// direction is open: (4, nil), W reads it), and W Closes with "more" from R
// unread, which sends a RST: R's Reads stay EOF (tcp_recvmsg_locked tests
// SOCK_DONE, set by the FIN, before sk_err: the RST's EPIPE is not returned),
// never bytes, never ECONNRESET; R's next Write fails (EPIPE: the RST in
// CLOSE_WAIT sets sk_err EPIPE, tcp_reset). Measured: EOF is sticky, also
// across a later RST, and a Write after EOF is not affected by it. The model
// already has it: EOF needs a direction with nothing unread and not open,
// which no outcome leaves (WriteOutcome appends only into an open direction).
func TestStickyEOF(t *testing.T) {
	t.Parallel()
	w, r := pair(t)
	mustWrite(t, w, "xyz")
	if err := w.CloseWrite(); err != nil {
		t.Fatal(err)
	}
	waitState(t, r, tcpCloseWait)
	got, at := stickyReads(t, r, 4)
	if got != "data:xyz EOF EOF EOF EOF EOF" || at != 0 {
		t.Fatalf("reads after FIN = %q (%d unread at EOF); want data:xyz then EOF x5, 0 unread", got, at)
	}
	if res := wres(r, "late"); res != "4,nil" {
		t.Fatalf("R's Write after its EOF = %s; want 4,nil (its direction is open)", res)
	}
	if s := readSeq(t, w, 1); s != "data:late" {
		t.Fatalf("W read %q; want data:late", s)
	}
	mustWrite(t, r, "more")
	waitInq(t, w, 4)
	if err := w.Close(); err != nil { // "more" unread: RST
		t.Fatal(err)
	}
	waitState(t, r, tcpClose)
	got, at = stickyReads(t, r, 3)
	if got != "EOF EOF EOF EOF" || at != 0 {
		t.Fatalf("R's reads after the RST that followed its EOF = %q; want EOF x4", got)
	}
	if res := wres(r, "x"); res != "0,EPIPE" {
		t.Fatalf("R's Write after the RST = %s; want 0,EPIPE", res)
	}
}

// TestStickyReset (D1: a cut, then an error, then EOF; D14 sys; the proposed
// sticky rule). B has received "hello", unread, when A Closes with B's byte
// unread (RST). B's Reads: "hello" (the received bytes survive the RST), then
// ECONNRESET with nothing unread (0 by SIOCINQ), then EOF on every later
// Read; a Read with an expired read deadline: the timeout (Go's prepareRead,
// before read(2)), no byte; an empty Read: (0, nil) at once (no read(2)); B's
// Writes: EPIPE, EPIPE. Measured: the error comes only once nothing is
// unread, and no byte follows it.
func TestStickyReset(t *testing.T) {
	t.Parallel()
	b, a := pair(t)
	mustWrite(t, a, "hello")
	waitInq(t, b, 5)
	resetBy(t, b, a)
	got, at := stickyReads(t, b, 4)
	if got != "data:hello ECONNRESET EOF EOF EOF EOF" || at != 0 {
		t.Fatalf("B's reads after the RST = %q (%d unread at the error); want data:hello ECONNRESET EOF x4, 0 unread", got, at)
	}
	b.SetReadDeadline(time.Now().Add(-time.Second))
	if n, err := b.Read(make([]byte, 8)); n != 0 || name(err) != "timeout" {
		t.Fatalf("Read with an expired deadline after the error = %d, %v; want 0, timeout", n, err)
	}
	b.SetReadDeadline(time.Time{})
	if n, err := b.Read(nil); n != 0 || err != nil {
		t.Fatalf("empty Read after the error = %d, %v; want 0, nil", n, err)
	}
	if got, at := stickyReads(t, b, 0); got != "EOF" || at != 0 {
		t.Fatalf("Read after those = %q; want EOF", got)
	}
	for i := 0; i < 2; i++ {
		if res := wres(b, "y"); res != "0,EPIPE" {
			t.Fatalf("B's Write %d after its read error = %s; want 0,EPIPE", i, res)
		}
	}
}

// TestStickyResetBlockedRead (D1, D14, the proposed sticky rule). B's Read is
// blocked, nothing unread, when A resets (SetLinger(0), Close): the Read
// returns ECONNRESET, and every later Read EOF. Measured: no byte follows.
func TestStickyResetBlockedRead(t *testing.T) {
	t.Parallel()
	b, a := pair(t)
	type res struct {
		n   int
		err error
	}
	ch := make(chan res, 1)
	go func() {
		b.SetReadDeadline(time.Now().Add(guard))
		n, err := b.Read(make([]byte, 8))
		ch <- res{n, err}
	}()
	// The RST finds the Read blocked or not yet made (no probe tells them
	// apart); either way it is the first Read after the RST, nothing unread.
	if err := a.SetLinger(0); err != nil {
		t.Fatal(err)
	}
	if err := a.Close(); err != nil {
		t.Fatal(err)
	}
	r := <-ch
	if r.n != 0 || name(r.err) != "ECONNRESET" {
		t.Fatalf("the blocked Read = %d, %v; want 0, ECONNRESET", r.n, r.err)
	}
	if at := inq(t, b); at != 0 {
		t.Fatalf("%d unread at the error", at)
	}
	if got := readSeq(t, b, 1) + " " + readSeq(t, b, 1) + " " + readSeq(t, b, 1); got != "EOF EOF EOF" {
		t.Fatalf("reads after the error = %q; want EOF x3", got)
	}
}

// TestStickyKilledPeer (D1, D10, D11, D14; the proposed sticky rule). The
// child writes "hello" and is killed (or exits) with the parent's byte "x"
// unread (its kernel sends RST). The parent's Reads: "hello", ECONNRESET with
// nothing unread, then EOF on every later Read; its Writes EPIPE. Measured:
// no byte follows the error.
func TestStickyKilledPeer(t *testing.T) {
	t.Parallel()
	for _, role := range []string{"dial-write-unread", "dial-write-unread-exit"} {
		t.Run(role, func(t *testing.T) {
			t.Parallel()
			ch, c := acceptFrom(t, role)
			waitInq(t, c, 5)
			mustWrite(t, c, "x")
			if ch.line(t) != "ready" {
				t.Fatal("child not ready")
			}
			ch.kill(t)
			waitState(t, c, tcpClose)
			got, at := stickyReads(t, c, 4)
			if got != "data:hello ECONNRESET EOF EOF EOF EOF" || at != 0 {
				t.Fatalf("reads after the dead child's RST = %q (%d unread at the error)", got, at)
			}
			if res := wres(c, "y"); res != "0,EPIPE" {
				t.Fatalf("Write after the read error = %s; want 0,EPIPE", res)
			}
		})
	}
}

// TestStickyOwnClose (D1: closed end: ErrClosed; D3; the proposed sticky
// rule). R has "abc" unread when it Closes its own end: every later Read
// returns ErrClosed (poll.FD's incref fails once closing), never the bytes;
// every Write ErrClosed. Measured: sticky (the model: NetEnd.closed, which
// nothing clears).
func TestStickyOwnClose(t *testing.T) {
	t.Parallel()
	w, r := pair(t)
	mustWrite(t, w, "abc")
	waitInq(t, r, 3)
	if err := r.Close(); err != nil {
		t.Fatal(err)
	}
	for i := 0; i < 3; i++ {
		if n, err := r.Read(make([]byte, 8)); n != 0 || name(err) != "ErrClosed" {
			t.Fatalf("Read %d after own Close = %d, %v; want 0, ErrClosed", i, n, err)
		}
	}
	if res := wres(r, "z"); res != "0,ErrClosed" {
		t.Fatalf("Write after own Close = %s; want 0,ErrClosed", res)
	}
}

// TestStickyNotTimeout (D1, D5: a timeout changes nothing; the exception to
// the proposed sticky rule). A Read blocked under a 20 ms read deadline
// returns the timeout; W then writes "abc": while the deadline is expired a
// Read returns the timeout at once with the bytes unread (3 by SIOCINQ);
// after SetReadDeadline(time.Time{}) the Read returns "abc", and a later one
// W's next bytes. Between the two, R's Write succeeds. Measured: a read
// deadline's timeout is not sticky (Go's poll.FD checks the deadline before
// read(2); the socket is untouched).
func TestStickyNotTimeout(t *testing.T) {
	t.Parallel()
	w, r := pair(t)
	r.SetReadDeadline(time.Now().Add(20 * time.Millisecond))
	if n, err := r.Read(make([]byte, 8)); n != 0 || name(err) != "timeout" {
		t.Fatalf("Read past its deadline = %d, %v; want 0, timeout", n, err)
	}
	mustWrite(t, w, "abc")
	waitInq(t, r, 3)
	if n, err := r.Read(make([]byte, 8)); n != 0 || name(err) != "timeout" || inq(t, r) != 3 {
		t.Fatalf("Read, deadline expired, bytes arrived = %d, %v; want 0, timeout, 3 unread", n, err)
	}
	if res := wres(r, "ok"); res != "2,nil" {
		t.Fatalf("R's Write after its timeout = %s; want 2,nil", res)
	}
	r.SetReadDeadline(time.Time{})
	if got := readSeq(t, r, 1); got != "data:abc" {
		t.Fatalf("Read after the timeout, deadline cleared = %q; want data:abc", got)
	}
	mustWrite(t, w, "de")
	waitInq(t, r, 2)
	if got := readSeq(t, r, 1); got != "data:de" {
		t.Fatalf("next Read = %q; want data:de", got)
	}
	if got := readSeq(t, w, 1); got != "data:ok" {
		t.Fatalf("W read %q; want data:ok", got)
	}
}
