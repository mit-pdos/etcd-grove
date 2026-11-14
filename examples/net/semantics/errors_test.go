//go:build linux

package semantics

import (
	"errors"
	"io"
	"net"
	"syscall"
	"testing"
	"time"
)

// TestErrorsAreOpErrors (the trusted models, NetTcp/TrustedCode/net.lean:
// "for any other failure an *OpError ... Op is Go's and Net is "tcp""; Read's
// end is io.EOF itself). Every failure of the modeled operations on values
// that Listen, Dial and Accept returned is an *net.OpError (never a bare
// error) with Net "tcp" and the model's Op: "read", "write", "close" (Close,
// CloseWrite, the listener's Close), "set" (the deadlines), "dial", "listen",
// "accept"; EOF is io.EOF unwrapped. Supports the models' error values.
// (Not covered by the claim: a zero TCPConn or TCPListener, whose methods
// return the bare syscall.EINVAL; the models do not give it, see
// notes/axiom-review/tcp-semantics.md.)
func TestErrorsAreOpErrors(t *testing.T) {
	t.Parallel()
	check := func(what, op string, err error) {
		t.Helper()
		var oe *net.OpError
		if !errors.As(err, &oe) || err != error(oe) {
			t.Errorf("%s: %T %v; want an *net.OpError", what, err, err)
			return
		}
		if oe.Op != op || oe.Net != "tcp" {
			t.Errorf("%s: Op %q Net %q; want %q, \"tcp\"", what, oe.Op, oe.Net, op)
		}
	}
	// a reset connection, then a closed one
	c, peer := pair(t)
	resetBy(t, c, peer)
	_, err := c.Write([]byte("x"))
	check("Write after RST", "write", err)
	_, err = c.Read(make([]byte, 1))
	if err != io.EOF {
		t.Errorf("Read after RST (its error taken by the Write): %v; want io.EOF", err)
	}
	check("CloseWrite after RST", "close", c.CloseWrite())
	c.Close()
	_, err = c.Read(make([]byte, 1))
	check("Read after Close", "read", err)
	_, err = c.Write(nil)
	check("Write after Close", "write", err)
	check("Close twice", "close", c.Close())
	check("CloseWrite after Close", "close", c.CloseWrite())
	check("SetDeadline after Close", "set", c.SetDeadline(time.Now()))
	check("SetReadDeadline after Close", "set", c.SetReadDeadline(time.Now()))
	check("SetWriteDeadline after Close", "set", c.SetWriteDeadline(time.Now()))
	// timeouts
	d, _ := pair(t)
	d.SetDeadline(time.Now())
	_, err = d.Read(make([]byte, 1))
	check("Read timeout", "read", err)
	_, err = d.Write([]byte("x"))
	check("Write timeout", "write", err)
	// listeners and dials
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	addr := ln.Addr().String()
	_, err = net.Listen("tcp", addr)
	check("Listen in use", "listen", err)
	ln.Close()
	_, err = ln.Accept()
	check("Accept after Close", "accept", err)
	check("listener Close twice", "close", ln.Close())
	// (refused unless another parallel test's listener or a forked child holds the port meanwhile)
	if c, err := net.Dial("tcp", addr); err != nil {
		check("Dial refused", "dial", err)
	} else {
		c.Close()
	}
}

// TestZeroValues (the trusted models' handles: "Go code outside net cannot
// make a conn ... so id is always an id the extension returned"). A program
// outside net can make a zero TCPConn or TCPListener (var c net.TCPConn):
// its fd is nil, and every method returns the bare syscall.EINVAL (not an
// *OpError) and touches no socket. In the models the zero value's id is 0,
// which names connection 0's dialer end, or listener 0, once Dial or Listen
// has chosen that number (DialStep, ListenStep allow it): an operation on it
// then acts on that connection or listener, where Go does nothing. Not a
// refutation (a proof cannot make the extension choose 0, and the operation
// is stuck otherwise), but more defined than Go
// (notes/axiom-review/tcp-semantics.md). Measured.
func TestZeroValues(t *testing.T) {
	t.Parallel()
	var c net.TCPConn
	var l net.TCPListener
	_, rerr := c.Read(make([]byte, 1))
	_, werr := c.Write([]byte("x"))
	_, aerr := l.Accept()
	errs := map[string]error{
		"Read": rerr, "Write": werr, "Close": c.Close(), "CloseWrite": c.CloseWrite(),
		"SetDeadline": c.SetDeadline(time.Now()), "Accept": aerr, "listener Close": l.Close(),
	}
	for op, err := range errs {
		if err != syscall.EINVAL {
			t.Errorf("zero value's %s: %T %v; want the bare syscall.EINVAL", op, err, err)
		}
	}
}
