//go:build linux

package semantics

import (
	"errors"
	"math"
	"net"
	"os"
	"syscall"
	"testing"
	"time"
)

// v3.3, D24: socket options (notes/dsverify-net-port-plan.md, phase 2).

// sockOpts are the socket options of D24, each applied to c; the bool says
// whether the method is conn's (Source nil, Addr laddr in its *OpError, as
// SetDeadline: SetReadBuffer, SetWriteBuffer) or TCPConn's own (Source laddr,
// Addr raddr).
func sockOpts(c *net.TCPConn) []struct {
	name   string
	isConn bool
	f      func() error
} {
	return []struct {
		name   string
		isConn bool
		f      func() error
	}{
		{"SetKeepAlive(true)", false, func() error { return c.SetKeepAlive(true) }},
		{"SetKeepAlive(false)", false, func() error { return c.SetKeepAlive(false) }},
		{"SetKeepAlivePeriod(30s)", false, func() error { return c.SetKeepAlivePeriod(30 * time.Second) }},
		{"SetKeepAlivePeriod(0)", false, func() error { return c.SetKeepAlivePeriod(0) }},
		{"SetReadBuffer(1<<20)", true, func() error { return c.SetReadBuffer(1 << 20) }},
		{"SetReadBuffer(0)", true, func() error { return c.SetReadBuffer(0) }},
		{"SetReadBuffer(-1)", true, func() error { return c.SetReadBuffer(-1) }},
		{"SetWriteBuffer(1<<20)", true, func() error { return c.SetWriteBuffer(1 << 20) }},
		{"SetWriteBuffer(-1)", true, func() error { return c.SetWriteBuffer(-1) }},
		{"SetWriteBuffer(MaxInt)", true, func() error { return c.SetWriteBuffer(math.MaxInt) }},
		{"SetNoDelay(true)", false, func() error { return c.SetNoDelay(true) }},
		{"SetNoDelay(false)", false, func() error { return c.SetNoDelay(false) }},
		{"SetLinger(5)", false, func() error { return c.SetLinger(5) }},
		{"SetLinger(-1)", false, func() error { return c.SetLinger(-1) }},
	}
}

// TestSockOpts (D24: socket options change no state the model has; on an end
// not closed they succeed, on a closed one they fail with net.ErrClosed, on the
// zero value they return syscall.EINVAL). SetKeepAlive, SetKeepAlivePeriod,
// SetReadBuffer, SetWriteBuffer, SetNoDelay and SetLinger are a setsockopt(2)
// through poll.FD.SetsockoptInt (fd.incref: ErrNetClosing once closing), their
// error an *OpError{Op: "set"} (TCPConn's: Source laddr, Addr raddr; conn's
// SetReadBuffer/SetWriteBuffer: Source nil, Addr laddr) around ErrNetClosing or
// an *os.SyscallError{"setsockopt"} (sockopt_posix.go, tcpsockopt_unix.go).
// Linux's SO_KEEPALIVE, SO_RCVBUF, SO_SNDBUF, SO_LINGER, TCP_NODELAY do not
// fail on a TCP socket in any state (sk_setsockopt clamps the buffer sizes),
// on either end (the acceptor's from an MPTCP listener, Go's default: the same),
// fresh, after the peer's FIN, after a reset, after CloseWrite. The one value
// Linux refuses: TCP_KEEPIDLE outside 1..32767 seconds (MAX_TCP_KEEPIDLE):
// SetKeepAlivePeriod(d) for d > 32767 s is EINVAL (d = 0 is Go's default 15 s,
// d < 0 returns nil before any system call, even on a closed end; Go rounds d
// up to seconds and passes the count through an int32). Measured.
func TestSockOpts(t *testing.T) {
	t.Parallel()
	check := func(what string, c *net.TCPConn) {
		for _, o := range sockOpts(c) {
			if err := o.f(); err != nil {
				t.Errorf("%s, %s = %v; want nil", what, o.name, err)
			}
		}
	}
	d, a := pair(t)
	check("dialer, fresh", d)
	check("acceptor, fresh", a)

	// both ends: the dialer's, and the acceptor's (from Go's default listener, MPTCP-capable)
	for _, acc := range []bool{false, true} {
		who := map[bool]string{false: "dialer", true: "acceptor"}[acc]
		pick := func(d, a *net.TCPConn) (me, peer *net.TCPConn) {
			if acc {
				return a, d
			}
			return d, a
		}
		me, peer := pick(pair(t))
		peer.Close()
		waitState(t, me, tcpCloseWait)
		check(who+", after the peer's FIN", me)
		if err := me.CloseWrite(); err != nil {
			t.Fatal(err)
		}
		check(who+", after FIN and CloseWrite", me)

		me, peer = pick(pair(t))
		if err := me.CloseWrite(); err != nil {
			t.Fatal(err)
		}
		check(who+", after its own CloseWrite", me)

		me, peer = pick(pair(t))
		resetBy(t, me, peer)
		check(who+", after a reset", me)
	}

	// a closed end: ErrClosed in an *OpError "set" with the method's addresses
	d4, _ := pair(t)
	la, ra := d4.LocalAddr(), d4.RemoteAddr()
	d4.Close()
	for _, o := range sockOpts(d4) {
		err := o.f()
		var oe *net.OpError
		if !errors.As(err, &oe) || oe.Op != "set" || !errors.Is(err, net.ErrClosed) || oe.Err != net.ErrClosed {
			t.Errorf("closed, %s = %v; want *OpError set, Err ErrClosed", o.name, err)
			continue
		}
		wantSrc, wantAddr := la, ra
		if o.isConn {
			wantSrc, wantAddr = nil, la
		}
		if oe.Source != wantSrc || oe.Addr != wantAddr {
			t.Errorf("closed, %s: Source %v Addr %v; want %v, %v", o.name, oe.Source, oe.Addr, wantSrc, wantAddr)
		}
	}
	if err := d4.SetKeepAlivePeriod(-time.Second); err != nil {
		t.Errorf("closed, SetKeepAlivePeriod(-1s) = %v; want nil (no system call)", err)
	}

	// TCP_KEEPIDLE's range
	d5, _ := pair(t)
	if err := d5.SetKeepAlivePeriod(32767 * time.Second); err != nil {
		t.Errorf("SetKeepAlivePeriod(32767s) = %v; want nil", err)
	}
	for _, p := range []time.Duration{32767*time.Second + 1, 32768 * time.Second, math.MaxInt64} {
		err := d5.SetKeepAlivePeriod(p)
		var se *os.SyscallError
		if !errors.As(err, &se) || se.Syscall != "setsockopt" || !errors.Is(err, syscall.EINVAL) {
			t.Errorf("SetKeepAlivePeriod(%v) = %v; want setsockopt EINVAL", p, err)
		}
	}
	// int32 truncation: 2^32 + 10 seconds is 10 seconds for the kernel
	if err := d5.SetKeepAlivePeriod((1<<32 + 10) * time.Second); err != nil {
		t.Errorf("SetKeepAlivePeriod((2^32+10)s) = %v; want nil (int32(secs) = 10)", err)
	}

	// the zero value: EINVAL, bare
	var z net.TCPConn
	for _, o := range sockOpts(&z) {
		if err := o.f(); err != syscall.EINVAL {
			t.Errorf("zero TCPConn, %s = %v; want syscall.EINVAL", o.name, err)
		}
	}
	if err := z.SetKeepAlivePeriod(-1); err != syscall.EINVAL {
		t.Errorf("zero TCPConn, SetKeepAlivePeriod(-1) = %v; want syscall.EINVAL", err)
	}
}
