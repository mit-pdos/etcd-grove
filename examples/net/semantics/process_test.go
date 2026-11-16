//go:build linux

package semantics

import (
	"net"
	"testing"
)

// The process-death tests: a child process (child_test.go) holds one end and
// is killed with SIGKILL, or exits (os.Exit, the "-exit" roles: D11). The
// kernel closes its sockets as close(2) would: FIN when nothing is unread,
// RST otherwise. In the model (D10, D11) a crash or exit does not touch the
// connections: the dead node's directions stay as they were (open), and
// what the peer sees must come from cuts (D1, D2).

// acceptFrom starts the child with the role, dialing a fresh listener of the
// parent, and returns the accepted end.
func acceptFrom(t *testing.T, role string) (*child, *net.TCPConn) {
	t.Helper()
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	ch := startChild(t, role, ln.Addr().String())
	c, err := ln.Accept()
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { c.Close() })
	return ch, c.(*net.TCPConn)
}

// TestKilledWriterFin (D10, D11; D1). The child writes "hello" and is killed
// (or exits), with nothing unread. Measured: the parent reads "hello", then
// EOF, with no error: the kernel sent FIN. The parent never wrote.
//
// REFUTES D1 + D10 as written: the child's direction stays open after the
// crash (D10), the child does not run Close or CloseWrite, so it can become
// fin or cut only by a cut, and D1 and D2 make a cut only inside a Read of
// that direction that returns an error (or a Write by the dead child).
// So "hello, EOF with no error first" is excluded, though D10 itself says
// "a cut that keeps every byte, then EOF, is a FIN". Needed: a cut that
// does not return an error (a Read's cut that then answers as on the cut
// direction: the kept bytes, EOF or error), or an environment step that
// cuts a dead node's directions.
func TestKilledWriterFin(t *testing.T) {
	t.Parallel()
	for _, role := range []string{"dial-write", "dial-write-exit"} {
		t.Run(role, func(t *testing.T) {
			t.Parallel()
			ch, c := acceptFrom(t, role)
			if ch.line(t) != "ready" {
				t.Fatal("child not ready")
			}
			ch.kill(t)
			waitState(t, c, tcpCloseWait)
			if got := readSeq(t, c, 4); got != "data:hello EOF" {
				t.Fatalf("reads of a dead writer's connection = %q; want data:hello EOF", got)
			}
		})
	}
}

// TestKilledWithUnreadInput (D10; D1). The child writes "hello"; the parent's
// byte "x" is unread in the child's receive buffer when it is killed: the
// kernel sends RST. Measured: the parent reads "hello" (the received bytes
// survive the RST), then ECONNRESET, then EOF. Allowed by D1 (a cut keeping
// the whole prefix, with the error, then EOF on a cut direction). Supports
// D1, D10.
func TestKilledWithUnreadInput(t *testing.T) {
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
			if got := readSeq(t, c, 5); got != "data:hello ECONNRESET EOF" {
				t.Fatalf("reads after the dead child's RST = %q; want data:hello ECONNRESET EOF", got)
			}
		})
	}
}

// TestKilledResetTakenByWrite (D10; D1, D2). As TestKilledWithUnreadInput,
// but the parent Writes first after the RST: the Write gets ECONNRESET, and
// the parent's reads are "hello" then EOF, with no read error.
//
// REFUTES D1 + D10 as written, as TestKilledWriterFin: the Write's cut is of
// the parent's own direction (D2), the child's direction stays open (no
// Close ran), so EOF with no read error before it is excluded. With a peer
// that Closed (TestResetErrorTakenByWrite) the same trace is allowed, its
// direction being fin. So EOF can follow a reset silently, with the reset
// seen only by a Write.
func TestKilledResetTakenByWrite(t *testing.T) {
	t.Parallel()
	ch, c := acceptFrom(t, "dial-write-unread")
	waitInq(t, c, 5)
	mustWrite(t, c, "x")
	if ch.line(t) != "ready" {
		t.Fatal("child not ready")
	}
	ch.kill(t)
	waitState(t, c, tcpClose)
	if _, err := c.Write([]byte("y")); name(err) != "ECONNRESET" {
		t.Fatalf("Write after the dead child's RST: %v; want ECONNRESET", err)
	}
	if got := readSeq(t, c, 5); got != "data:hello EOF" {
		t.Fatalf("reads after the Write took the reset = %q; want data:hello EOF", got)
	}
}

// TestWriteToKilledPeer (D10; D2: "d open: all of bs appended, nil"; "d cut:
// ... nil or error"). The child is killed with nothing unread (FIN). The
// parent's next Write succeeds and its bytes are lost (the child's port
// answers with RST); once the RST has arrived, every Write fails with EPIPE
// (the RST came in CLOSE_WAIT: tcp_reset sets EPIPE). Supports D2.
func TestWriteToKilledPeer(t *testing.T) {
	t.Parallel()
	ch, c := acceptFrom(t, "dial-write")
	if ch.line(t) != "ready" {
		t.Fatal("child not ready")
	}
	ch.kill(t)
	waitState(t, c, tcpCloseWait)
	if n, err := c.Write([]byte("lost")); n != 4 || err != nil {
		t.Fatalf("Write to a dead peer = %d, %v; want 4, nil (bytes lost)", n, err)
	}
	waitState(t, c, tcpClose)
	for i := 0; i < 2; i++ {
		if n, err := c.Write([]byte("x")); n != 0 || name(err) != "EPIPE" {
			t.Fatalf("Write %d after the RST = %d, %v; want 0, EPIPE", i, n, err)
		}
	}
}

// TestServerKilledBeforeReply (D10, D11; D1). A server process accepts, reads
// the client's whole 4-byte request, and is killed before writing its reply.
// Measured: the client's reads return EOF with no bytes and no error (the
// kernel's FIN: nothing was unread at the server). The client cannot tell
// this from a server that replied with nothing and closed.
//
// REFUTES D1 + D10 as written, as TestKilledWriterFin: the server's
// direction stays open after its crash, so EOF needs a cut, and a cut
// returns an error.
func TestServerKilledBeforeReply(t *testing.T) {
	t.Parallel()
	for _, role := range []string{"serve-read", "serve-read-exit"} {
		t.Run(role, func(t *testing.T) {
			t.Parallel()
			ch := startChild(t, role, "")
			c, err := net.Dial("tcp", ch.line(t))
			if err != nil {
				t.Fatal(err)
			}
			defer c.Close()
			mustWrite(t, c, "req!")
			if ch.line(t) != "got" {
				t.Fatal("server did not read the request")
			}
			ch.kill(t)
			waitState(t, c.(*net.TCPConn), tcpCloseWait)
			if got := readSeq(t, c, 3); got != "EOF" {
				t.Fatalf("client's reads after the server died = %q; want EOF", got)
			}
		})
	}
}

// TestKilledListener (D10: "its listeners are gone"; D7, D8). A child listens
// and never accepts; the parent's Dial succeeds (the kernel queues it). When
// the child is killed, the queued connection is reset (the parent reads
// ECONNRESET, then EOF) and the address refuses new Dials (ECONNREFUSED).
// Supports D10 (listeners gone), D8 (failure); the model's leaving the
// connection pending (D7) is more than Linux.
func TestKilledListener(t *testing.T) {
	t.Parallel()
	ch := startChild(t, "listen", "")
	addr := ch.line(t)
	c, err := net.Dial("tcp", addr)
	if err != nil {
		t.Fatalf("Dial of a listener that never accepts: %v; want success", err)
	}
	defer c.Close()
	ch.kill(t)
	waitState(t, c.(*net.TCPConn), tcpClose)
	if got := readSeq(t, c, 3); got != "ECONNRESET EOF" {
		t.Fatalf("reads after the listener's process died = %q; want ECONNRESET EOF", got)
	}
	if c2, err := net.Dial("tcp", addr); name(err) != "ECONNREFUSED" {
		if c2 != nil {
			c2.Close()
		}
		t.Fatalf("Dial after the listener's process died: %v; want ECONNREFUSED", err)
	}
}
