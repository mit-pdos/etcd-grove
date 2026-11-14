//go:build linux

package semantics

import (
	"errors"
	"net"
	"testing"
	"time"
)

// TestCloseTwice (D3: "closed: error, nothing"; otherwise closed := true,
// result nil or error; D1/D2/D4/D5: every operation on a closed end is an
// error). Measured: the first Close returns nil, sends FIN (the peer reads
// EOF); a second Close, and Read, Write, CloseWrite, SetDeadline,
// SetReadDeadline, SetWriteDeadline after it all return an error with
// errors.Is(err, net.ErrClosed) ("use of closed network connection": Go's
// fd mutex refuses, no system call is made). Supports D1-D5.
func TestCloseTwice(t *testing.T) {
	t.Parallel()
	c, peer := pair(t)
	if err := c.Close(); err != nil {
		t.Fatalf("first Close: %v; want nil", err)
	}
	if got := readSeq(t, peer, 2); got != "EOF" {
		t.Fatalf("peer after Close: %q; want EOF", got)
	}
	ops := map[string]error{
		"Close":            c.Close(),
		"CloseWrite":       c.CloseWrite(),
		"SetDeadline":      c.SetDeadline(time.Now()),
		"SetReadDeadline":  c.SetReadDeadline(time.Time{}),
		"SetWriteDeadline": c.SetWriteDeadline(time.Now()),
	}
	_, ops["Read"] = c.Read(make([]byte, 4))
	_, ops["Write"] = c.Write([]byte("x"))
	for op, err := range ops {
		if !errors.Is(err, net.ErrClosed) {
			t.Errorf("%s after Close: %v; want an error that Is net.ErrClosed", op, err)
		}
	}
}

// TestCloseUnblocksRead (D1: "closed end: error"; D3). A Read blocked on an
// open, empty direction returns ErrClosed when its own end is Closed by
// another goroutine (the model: the Read waits; Close; the Read's step
// then sees a closed end). Supports D1, D3.
func TestCloseUnblocksRead(t *testing.T) {
	t.Parallel()
	c, _ := pair(t)
	done := make(chan error, 1)
	go func() {
		_, err := c.Read(make([]byte, 4))
		done <- err
	}()
	time.Sleep(10 * time.Millisecond) // lets the Read block; the outcome is the same if it has not
	c.Close()
	select {
	case err := <-done:
		if !errors.Is(err, net.ErrClosed) {
			t.Fatalf("blocked Read after own Close: %v; want ErrClosed", err)
		}
	case <-time.After(waitLimit):
		t.Fatal("Read still blocked after Close")
	}
}

// TestCloseAfterReset (D3: "result nil or error (the end is closed either
// way)"). Close of an end whose connection has been reset (the socket is in
// CLOSE, the error pending) returns nil: close(2) does not report sk_err.
// Before it, SetDeadline on the reset end returns nil (D5: only a closed
// end errs; deadlines are Go's, no system call). Supports D3 (nil; the
// error alternative is not observed here), D5.
func TestCloseAfterReset(t *testing.T) {
	t.Parallel()
	c, peer := pair(t)
	resetBy(t, c, peer)
	if err := c.SetDeadline(time.Now().Add(time.Hour)); err != nil {
		t.Fatalf("SetDeadline after RST: %v; want nil", err)
	}
	if err := c.Close(); err != nil {
		t.Fatalf("Close after RST: %v; want nil", err)
	}
}

// TestCloseWrite (D4: d open -> fin, nil; D2: "d fin (own CloseWrite): error
// (EPIPE)"; D1 on the other direction). A writes "abc" and CloseWrites:
// nil; B reads "abc" then EOF. A's Write after its CloseWrite fails with
// EPIPE (tcp_sendmsg: SEND_SHUTDOWN). A still reads: B's "back" arrives.
// A second CloseWrite returns nil while the peer's direction is open
// (shutdown(SHUT_WR) in FIN_WAIT does nothing), and ENOTCONN once both
// sides have sent FIN (the socket is in TIME_WAIT, TCP_CLOSE to
// inet_shutdown). Supports D1, D2, D4 (on fin: nil, or an error that
// changes nothing).
func TestCloseWrite(t *testing.T) {
	t.Parallel()
	a, b := pair(t)
	mustWrite(t, a, "abc")
	if err := a.CloseWrite(); err != nil {
		t.Fatalf("CloseWrite: %v", err)
	}
	if got := readSeq(t, b, 3); got != "data:abc EOF" {
		t.Fatalf("B's reads = %q; want data:abc EOF", got)
	}
	if err := a.CloseWrite(); err != nil {
		t.Fatalf("second CloseWrite, B's direction open: %v; want nil", err)
	}
	if _, err := a.Write([]byte("x")); name(err) != "EPIPE" {
		t.Fatalf("Write after own CloseWrite: %v; want EPIPE", err)
	}
	mustWrite(t, b, "back")
	if err := b.CloseWrite(); err != nil {
		t.Fatal(err)
	}
	if got := readSeq(t, a, 3); got != "data:back EOF" {
		t.Fatalf("A's reads after its own CloseWrite = %q; want data:back EOF", got)
	}
	if err := a.CloseWrite(); name(err) != "ENOTCONN" {
		t.Fatalf("third CloseWrite, both sides fin: %v; want ENOTCONN", err)
	}
}

// TestCloseWriteAfterReset (D4: "d fin/cut: unchanged, nil or error").
// CloseWrite of an end whose connection has been reset returns ENOTCONN
// (inet_shutdown on a TCP_CLOSE socket), without consuming the reset error
// (the next Read still gets ECONNRESET). Supports D4 (the error
// alternative).
func TestCloseWriteAfterReset(t *testing.T) {
	t.Parallel()
	c, peer := pair(t)
	resetBy(t, c, peer)
	if err := c.CloseWrite(); name(err) != "ENOTCONN" {
		t.Fatalf("CloseWrite after RST: %v; want ENOTCONN", err)
	}
	if got := readSeq(t, c, 3); got != "ECONNRESET EOF" {
		t.Fatalf("reads = %q; want ECONNRESET EOF", got)
	}
}
