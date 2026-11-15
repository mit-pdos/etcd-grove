//go:build linux

package semantics

import (
	"testing"
)

// TestResetCloseUnreadInput (D1: "any time: d is cut, keeping a prefix of its
// unread bytes; error", then "no bytes, d is cut: EOF or error"; D3). Peer A
// writes "hello", which arrives at B; B's byte "u" is unread at A when A
// Closes, so A's kernel sends RST instead of FIN (RFC 2525 2.17). Measured on
// B: the bytes received before the RST survive it (tcp_reset purges the
// write queue, not the receive queue); then ECONNRESET once (sock_error
// clears sk_err); then EOF (the socket is shut down both ways). Supports D1
// (a cut that keeps the whole prefix, the error, then EOF) and D3 (A's Close
// returns nil although it reset).
func TestResetCloseUnreadInput(t *testing.T) {
	t.Parallel()
	b, a := pair(t)
	mustWrite(t, a, "hello")
	waitInq(t, b, 5)
	resetBy(t, b, a)
	if got := readSeq(t, b, 5); got != "data:hello ECONNRESET EOF" {
		t.Fatalf("B's reads after A's reset = %q", got)
	}
}

// TestResetLingerZero (D1, D3). SetLinger(0) then Close sends RST whatever is
// unread (and drops A's unsent output; on loopback "hello" has been delivered
// before). Measured: as TestResetCloseUnreadInput, the received bytes, then
// ECONNRESET, then EOF. Supports D1.
func TestResetLingerZero(t *testing.T) {
	t.Parallel()
	b, a := pair(t)
	mustWrite(t, a, "hello")
	waitInq(t, b, 5)
	if err := a.SetLinger(0); err != nil {
		t.Fatal(err)
	}
	if err := a.Close(); err != nil {
		t.Fatalf("Close with linger 0: %v; want nil", err)
	}
	waitState(t, b, tcpClose)
	if got := readSeq(t, b, 5); got != "data:hello ECONNRESET EOF" {
		t.Fatalf("B's reads after A's linger-0 Close = %q", got)
	}
}

// TestResetErrorTakenByWrite (D1: "no bytes, d is cut: EOF or error"; D2). The
// reset error is one pending sk_err, delivered to whichever call comes
// first: here B's Write gets ECONNRESET, and every later Read of B gets the
// bytes still queued, then EOF, with no error. So a reader can see a reset
// connection end in EOF silently, when another goroutine's Write (or Read)
// took the error. Here A had Closed (its direction is fin in the model),
// so the trace is allowed by D1's fin clause alone. Then B's writes fail
// with EPIPE (the error is gone, the socket is shut down). Supports D1, D2.
// See TestKilledResetTakenByWrite for the same with a killed peer, where no
// Close happened.
func TestResetErrorTakenByWrite(t *testing.T) {
	t.Parallel()
	b, a := pair(t)
	mustWrite(t, a, "hi")
	waitInq(t, b, 2)
	resetBy(t, b, a)
	if _, err := b.Write([]byte("y")); name(err) != "ECONNRESET" {
		t.Fatalf("B's first Write after RST: %v; want ECONNRESET", err)
	}
	if got := readSeq(t, b, 5); got != "data:hi EOF" {
		t.Fatalf("B's reads after its Write took the error = %q; want data:hi EOF", got)
	}
	if _, err := b.Write([]byte("z")); name(err) != "EPIPE" {
		t.Fatalf("B's second Write after RST: %v; want EPIPE", err)
	}
}

// TestWriteAfterPeerClose (D2: "d open: all of bs appended, nil", then a cut;
// "d cut: bs discarded; nil or error"). A Closes with nothing unread (FIN).
// B's Write still succeeds: the bytes go out and are lost (A's kernel answers
// with RST, the socket being closed). Once the RST has arrived, no Write
// succeeds: every one fails with EPIPE (a RST received in CLOSE_WAIT sets
// sk_err to EPIPE, not ECONNRESET: tcp_reset), so Linux never returns nil
// for a Write after it has received the RST (D2 allows nil there: more than
// Linux, which is sound). B's Read: since A's FIN came first, EOF, with no
// error (tcp_recvmsg checks SOCK_DONE before sk_err). Supports D2, D1 (fin:
// EOF).
func TestWriteAfterPeerClose(t *testing.T) {
	t.Parallel()
	b, a := pair(t)
	if err := a.Close(); err != nil {
		t.Fatal(err)
	}
	waitState(t, b, tcpCloseWait)
	if n, err := b.Write([]byte("lost")); n != 4 || err != nil {
		t.Fatalf("B's Write after A's FIN = %d, %v; want 4, nil (bytes lost)", n, err)
	}
	waitState(t, b, tcpClose)
	if got := readSeq(t, b, 3); got != "EOF" {
		t.Fatalf("B's reads after FIN then RST = %q; want EOF", got)
	}
	for i := 0; i < 2; i++ {
		if n, err := b.Write([]byte("x")); n != 0 || name(err) != "EPIPE" {
			t.Fatalf("B's Write %d after the RST = %d, %v; want 0, EPIPE", i, n, err)
		}
	}
}

// TestPartialWriteOnReset (D2: "d open: ... or a prefix appended and d cut,
// error"). B writes 64 MiB while A reads a little, then resets (linger 0).
// Measured: B's Write returns 0 < n < len with ECONNRESET (or EPIPE, when
// the RST lands between two write(2)s of Go's loop); n counts what the
// kernel took, which is more than A read. Supports D2 (a prefix, then an
// error), and shows that n says nothing of what the peer read.
func TestPartialWriteOnReset(t *testing.T) {
	t.Parallel()
	b, a := pair(t)
	const size = 64 << 20
	type res struct {
		n   int
		err error
	}
	ch := make(chan res, 1)
	go func() {
		n, err := b.Write(make([]byte, size))
		ch <- res{n, err}
	}()
	buf := make([]byte, 64<<10)
	if _, err := a.Read(buf); err != nil {
		t.Fatal(err)
	}
	waitInq(t, a, 1)
	a.SetLinger(0)
	a.Close()
	r := <-ch
	t.Logf("partial write: n = %d of %d, err = %v", r.n, size, r.err)
	if r.n <= 0 || r.n >= size || (name(r.err) != "ECONNRESET" && name(r.err) != "EPIPE") {
		t.Fatalf("Write during reset = %d, %v; want 0 < n < %d, ECONNRESET or EPIPE", r.n, r.err, size)
	}
}
