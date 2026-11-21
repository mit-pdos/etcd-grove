//go:build linux

package semantics

import (
	"errors"
	"net"
	"strconv"
	"testing"
	"time"
)

// v3.3, D23: the network "tcp4" (notes/dsverify-net-port-plan.md, phase 2).

func itoa(n int) string { return strconv.Itoa(n) }

// opErrNet is the Net field of err, an *OpError, or "" if err is not one.
func opErrNet(err error) string {
	var oe *net.OpError
	if errors.As(err, &oe) {
		return oe.Net
	}
	return ""
}

// TestTcp4 (D23: "tcp4" behaves as "tcp" on the valid IPv4 addresses, the
// network's name in the errors' Net). Listen("tcp4", a) and Dial("tcp4", a),
// DialTimeout("tcp4", a, d) of an IPv4 address connect as "tcp" does; every
// *OpError carries Go's network string: Dial's and Listen's the one passed
// (dial.go: &OpError{Op: "dial", Net: d.network ...}, sysListener's
// lc.network), a connection's that of the Dial or of the listener that
// accepted it (netFD.net: newFD(..., fd.net) in netFD.accept), as do its Read,
// Write, Close, SetDeadline, CloseWrite and SetKeepAlive errors. A Dial of
// "tcp" to a "tcp4" listener and the reverse interoperate (one TCP).
// Measured.
func TestTcp4(t *testing.T) {
	t.Parallel()
	ln, err := net.Listen("tcp4", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("Listen tcp4: %v", err)
	}
	defer ln.Close()
	addr := ln.Addr().String()
	if _, err := net.Listen("tcp4", addr); opErrNet(err) != "tcp4" || name(err) != "EADDRINUSE" {
		t.Fatalf("second Listen tcp4 = %v (Net %q); want EADDRINUSE, Net tcp4", err, opErrNet(err))
	}
	for _, nw := range []string{"tcp4", "tcp"} {
		ch := make(chan net.Conn, 1)
		go func() {
			c, err := ln.Accept()
			if err != nil {
				t.Errorf("Accept: %v", err)
			}
			ch <- c
		}()
		var dc net.Conn
		if nw == "tcp4" {
			dc, err = net.DialTimeout(nw, addr, guard)
		} else {
			dc, err = net.Dial(nw, addr)
		}
		if err != nil {
			t.Fatalf("Dial %s: %v", nw, err)
		}
		ac := <-ch
		mustWrite(t, dc, "hi")
		if got := readSeq(t, ac, 1); got != "data:hi" {
			t.Fatalf("%s: read %q", nw, got)
		}
		dc.Close()
		ac.Close()
		// the dialer's errors carry the Dial's network, the acceptor's the listener's
		for _, x := range []struct {
			c  net.Conn
			nw string
		}{{dc, nw}, {ac, "tcp4"}} {
			if _, err := x.c.Read(make([]byte, 1)); opErrNet(err) != x.nw || name(err) != "ErrClosed" {
				t.Errorf("Read after Close = %v (Net %q); want ErrClosed, Net %s", err, opErrNet(err), x.nw)
			}
			if _, err := x.c.Write([]byte("x")); opErrNet(err) != x.nw {
				t.Errorf("Write after Close = %v (Net %q); want Net %s", err, opErrNet(err), x.nw)
			}
			if err := x.c.Close(); opErrNet(err) != x.nw {
				t.Errorf("Close after Close = %v (Net %q); want Net %s", err, opErrNet(err), x.nw)
			}
			if err := x.c.SetDeadline(time.Now()); opErrNet(err) != x.nw {
				t.Errorf("SetDeadline after Close = %v (Net %q); want Net %s", err, opErrNet(err), x.nw)
			}
			if err := x.c.(*net.TCPConn).CloseWrite(); opErrNet(err) != x.nw {
				t.Errorf("CloseWrite after Close = %v (Net %q); want Net %s", err, opErrNet(err), x.nw)
			}
			if err := x.c.(*net.TCPConn).SetKeepAlive(true); opErrNet(err) != x.nw {
				t.Errorf("SetKeepAlive after Close = %v (Net %q); want Net %s", err, opErrNet(err), x.nw)
			}
		}
	}
	ln.Close()
	if _, err := ln.Accept(); opErrNet(err) != "tcp4" || name(err) != "ErrClosed" {
		t.Fatalf("Accept after Close = %v (Net %q); want ErrClosed, Net tcp4", err, opErrNet(err))
	}
	if err := ln.Close(); opErrNet(err) != "tcp4" {
		t.Fatalf("listener Close after Close = %v (Net %q); want Net tcp4", err, opErrNet(err))
	}
	// the wildcards of D21 with "tcp4": every IPv4 address ("[::]" too), as "tcp"'s
	for _, w := range []string{":0", "0.0.0.0:0", "[::]:0"} {
		wl, err := net.Listen("tcp4", w)
		if err != nil {
			t.Fatalf("Listen tcp4 %q: %v", w, err)
		}
		port := wl.Addr().(*net.TCPAddr).Port
		c, err := net.Dial("tcp4", net.JoinHostPort("127.0.0.1", itoa(port)))
		if err != nil {
			t.Fatalf("Dial of tcp4 wildcard %q's port: %v", w, err)
		}
		c.Close()
		wl.Close()
	}
	// a refused dial: Net is the Dial's network
	for _, nw := range []string{"tcp4", "tcp"} {
		if _, err := net.Dial(nw, addr); opErrNet(err) != nw || name(err) != "ECONNREFUSED" {
			t.Errorf("Dial %s, no listener = %v (Net %q); want ECONNREFUSED, Net %s", nw, err, opErrNet(err), nw)
		}
		if _, err := net.DialTimeout(nw, addr, guard); opErrNet(err) != nw || name(err) != "ECONNREFUSED" {
			t.Errorf("DialTimeout %s, no listener = %v (Net %q); want ECONNREFUSED, Net %s", nw, err, opErrNet(err), nw)
		}
	}
}
