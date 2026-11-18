//go:build linux

package semantics

// The tests of the v3 decisions (notes/net-tcp-v3-plan.md): the error
// identities (D14), the Write/Close race (D15), abandoned dials (D16), Close
// of an open end or listener (D17), the addresses (D18), DialTimeout (D19).
// Each is indexed in doc.go with its Lean definition and Tests.lean example.

import (
	"errors"
	"io"
	"net"
	"os"
	"strconv"
	"sync"
	"syscall"
	"testing"
	"time"
)

// opErr is err as an *net.OpError, or fails the test.
func opErr(t *testing.T, what string, err error) *net.OpError {
	t.Helper()
	oe, ok := err.(*net.OpError)
	if !ok {
		t.Fatalf("%s: %T %v; want an *net.OpError", what, err, err)
	}
	return oe
}

// TestErrClosed (D14, Impl.lean NetErr.closed; TrustedCode/net.lean
// model.closedErr, OpError.Timeout/Temporary). An operation on one's own
// closed end or listener fails with an *OpError whose Err is
// poll.ErrNetClosing, so errors.Is(err, net.ErrClosed) is true, and
// Timeout() and Temporary() are false: Read, Write, SetDeadline, CloseWrite
// and a second Close of a closed connection; Accept and a second Close of a
// closed listener; a Read and an Accept blocked when another goroutine closed
// it. errors.Is(err, net.ErrClosed) is false for every other failure: io.EOF,
// a deadline's timeout, ECONNRESET, EADDRINUSE, ECONNREFUSED. (Ported from
// dsverify-lab harness/netsem/err_closed.go.) Measured.
func TestErrClosed(t *testing.T) {
	t.Parallel()
	closed := func(what string, err error) {
		t.Helper()
		if !errors.Is(err, net.ErrClosed) {
			t.Errorf("%s: %v; want an error that Is net.ErrClosed", what, err)
			return
		}
		oe := opErr(t, what, err)
		if oe.Err != net.ErrClosed {
			t.Errorf("%s: Err %T %v; want net.ErrClosed itself", what, oe.Err, oe.Err)
		}
		if oe.Timeout() || oe.Temporary() {
			t.Errorf("%s: Timeout %v Temporary %v; want false, false", what, oe.Timeout(), oe.Temporary())
		}
	}
	notClosed := func(what string, err error) {
		t.Helper()
		if err == nil || errors.Is(err, net.ErrClosed) {
			t.Errorf("%s: %v; want an error that is not net.ErrClosed", what, err)
		}
	}
	d, a := pair(t)
	if err := d.Close(); err != nil {
		t.Fatal(err)
	}
	_, err := d.Read(make([]byte, 4))
	closed("Read", err)
	_, err = d.Write([]byte("x"))
	closed("Write", err)
	closed("SetDeadline", d.SetDeadline(time.Now()))
	closed("CloseWrite", d.CloseWrite())
	closed("Close again", d.Close())
	a.SetReadDeadline(time.Now().Add(guard))
	_, err = a.Read(make([]byte, 4))
	if err != io.EOF {
		t.Errorf("peer's Read: %v; want io.EOF", err)
	}
	notClosed("peer's EOF", err)

	d, a = pair(t)
	d.SetReadDeadline(time.Now())
	_, err = d.Read(make([]byte, 4))
	notClosed("timeout", err)
	ch := make(chan error, 1)
	go func() { _, e := a.Read(make([]byte, 4)); ch <- e }()
	time.Sleep(20 * time.Millisecond) // lets the Read block; the outcome is the same if it has not
	a.Close()
	closed("blocked Read", <-ch)

	c, peer := pair(t)
	resetBy(t, c, peer)
	_, err = c.Read(make([]byte, 4))
	notClosed("ECONNRESET", err)

	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	addr := ln.Addr().String()
	_, err = net.Listen("tcp", addr)
	notClosed("EADDRINUSE", err)
	go func() { _, e := ln.Accept(); ch <- e }()
	time.Sleep(20 * time.Millisecond)
	if err := ln.Close(); err != nil {
		t.Fatal(err)
	}
	closed("blocked Accept", <-ch)
	_, err = ln.Accept()
	closed("Accept", err)
	closed("listener Close again", ln.Close())
	forkMu.RLock()
	if c, err := net.Dial("tcp", addr); err != nil {
		notClosed("ECONNREFUSED", err)
	} else {
		c.Close()
	}
	forkMu.RUnlock()
}

// TestDeadlineErrors (D14, Impl.lean NetErr.timeout; TrustedCode/net.lean
// model.deadlineErr, OpError.Timeout/Temporary). A Read or a Write past its
// deadline fails with an *OpError whose Err is os.ErrDeadlineExceeded itself
// (the pointer poll.ErrDeadlineExceeded), so errors.Is(err,
// os.ErrDeadlineExceeded) is true, Timeout() and Temporary() are true, and it
// is not net.ErrClosed. Measured.
func TestDeadlineErrors(t *testing.T) {
	t.Parallel()
	d, _ := pair(t)
	check := func(what string, err error) {
		t.Helper()
		oe := opErr(t, what, err)
		if oe.Err != os.ErrDeadlineExceeded || !errors.Is(err, os.ErrDeadlineExceeded) {
			t.Errorf("%s: Err %T %v; want os.ErrDeadlineExceeded itself", what, oe.Err, oe.Err)
		}
		if !oe.Timeout() || !oe.Temporary() {
			t.Errorf("%s: Timeout %v Temporary %v; want true, true", what, oe.Timeout(), oe.Temporary())
		}
		if errors.Is(err, net.ErrClosed) {
			t.Errorf("%s: Is net.ErrClosed", what)
		}
	}
	d.SetReadDeadline(time.Now())
	_, err := d.Read(make([]byte, 4))
	check("Read", err)
	d.SetWriteDeadline(time.Now())
	_, err = d.Write([]byte("x"))
	check("Write", err)
}

// TestSyscallErrors (D14, Impl.lean NetErr.sys; TrustedCode/net.lean
// model.sysErr, the module docstring's syscall names and OpError addresses).
// Every other failure's Err is an *os.SyscallError wrapping a syscall.Errno,
// with Go's system call name: ECONNRESET from "read", EPIPE from "write",
// ENOTCONN from "shutdown" (CloseWrite), ECONNREFUSED from "connect" (Dial),
// EADDRINUSE from "bind" (Listen). The OpError's Source and Addr: the end's
// LocalAddr and RemoteAddr for Read, Write, CloseWrite; nil and a *TCPAddr
// for Dial and Listen; nil and LocalAddr for the deadlines; nil and the
// listener's Addr for Accept. Measured.
func TestSyscallErrors(t *testing.T) {
	t.Parallel()
	sys := func(what string, err error, call string, errno syscall.Errno) *net.OpError {
		t.Helper()
		oe := opErr(t, what, err)
		se, ok := oe.Err.(*os.SyscallError)
		if !ok {
			t.Errorf("%s: Err %T %v; want an *os.SyscallError", what, oe.Err, oe.Err)
			return oe
		}
		if e, ok := se.Err.(syscall.Errno); !ok || e != errno || se.Syscall != call {
			t.Errorf("%s: %q %T %v; want %q %v", what, se.Syscall, se.Err, se.Err, call, errno)
		}
		return oe
	}
	ends := func(what string, oe *net.OpError, c net.Conn) {
		t.Helper()
		if oe.Source != c.LocalAddr() || oe.Addr != c.RemoteAddr() {
			t.Errorf("%s: Source %v Addr %v; want the end's LocalAddr, RemoteAddr", what, oe.Source, oe.Addr)
		}
	}
	c, peer := pair(t)
	resetBy(t, c, peer)
	_, err := c.Read(make([]byte, 4))
	ends("Read", sys("Read after RST", err, "read", syscall.ECONNRESET), c)
	_, err = c.Write([]byte("x"))
	ends("Write", sys("Write after RST", err, "write", syscall.EPIPE), c)
	ends("CloseWrite", sys("CloseWrite after RST", c.CloseWrite(), "shutdown", syscall.ENOTCONN), c)

	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	addr := ln.Addr().String()
	_, err = net.Listen("tcp", addr)
	oe := sys("Listen in use", err, "bind", syscall.EADDRINUSE)
	if _, ok := oe.Addr.(*net.TCPAddr); oe.Source != nil || !ok {
		t.Errorf("Listen: Source %v Addr %T; want nil, a *TCPAddr", oe.Source, oe.Addr)
	}
	ln.Close()
	_, err = ln.Accept()
	oe = opErr(t, "Accept", err)
	if oe.Source != nil || oe.Addr != ln.Addr() {
		t.Errorf("Accept: Source %v Addr %v; want nil, the listener's Addr", oe.Source, oe.Addr)
	}
	forkMu.RLock()
	if c, err := net.Dial("tcp", addr); err != nil {
		oe = sys("Dial refused", err, "connect", syscall.ECONNREFUSED)
		if a, ok := oe.Addr.(*net.TCPAddr); oe.Source != nil || !ok || a == nil {
			t.Errorf("Dial: Source %v Addr %T; want nil, a non-nil *TCPAddr", oe.Source, oe.Addr)
		}
	} else {
		c.Close()
	}
	forkMu.RUnlock()

	d, _ := pair(t)
	d.Close()
	oe = opErr(t, "SetDeadline", d.SetDeadline(time.Now()))
	if oe.Source != nil || oe.Addr != d.LocalAddr() {
		t.Errorf("SetDeadline: Source %v Addr %v; want nil, LocalAddr", oe.Source, oe.Addr)
	}
}

// TestWriteCloseRace (D15: a Write is a loop of steps, Impl.lean WriteOutcome;
// v3 had a disjunct for it). A Write blocked for buffer space (64 MiB to a
// peer that does not read yet) when another goroutine Closes the same end
// returns 0 < k < len with net.ErrClosed, and the peer reads exactly those k
// bytes, then io.EOF: Go's poll.FD.Write loops over write(2), and its
// waitWrite, woken by the Close (pd.evict), returns ErrNetClosing with the
// count so far; the socket is closed (FIN after the bytes) when the Write
// releases it. In the model the Write's earlier steps append the k bytes, the
// Close shuts the direction after them, and the next step fails closed.
// (Ported from dsverify-lab harness/netsem/write_close_race.go.) Measured.
func TestWriteCloseRace(t *testing.T) {
	t.Parallel()
	d, a := pair(t)
	big := make([]byte, 64<<20)
	go func() {
		time.Sleep(100 * time.Millisecond)
		d.Close()
	}()
	k, err := d.Write(big)
	if !(0 < k && k < len(big)) || !errors.Is(err, net.ErrClosed) {
		t.Fatalf("Write = %d of %d, %v; want 0 < k < len, ErrClosed", k, len(big), err)
	}
	got := 0
	buf := make([]byte, 1<<20)
	a.SetReadDeadline(time.Now().Add(10 * guard))
	for {
		n, err := a.Read(buf)
		got += n
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatalf("peer's Read after %d bytes: %v; want the bytes, then io.EOF", got, err)
		}
	}
	if got != k {
		t.Fatalf("peer read %d bytes; the Write returned %d", got, k)
	}
}

// TestCloseOpenNil (D17, Impl.lean CloseOutcome, LisCloseOutcome). Close of
// an open end returns nil whatever its connection's state: fresh, after the
// peer's Close (FIN), after its own CloseWrite, after a reset, with a Read
// blocked on it; Close of an open listener returns nil, also with an Accept
// blocked on it (poll.FD.Close fails only on a closing fd; close(2) of a
// socket returns 0). Measured.
func TestCloseOpenNil(t *testing.T) {
	t.Parallel()
	c, _ := pair(t)
	if err := c.Close(); err != nil {
		t.Errorf("Close, fresh: %v", err)
	}
	c, p := pair(t)
	p.Close()
	if got := readSeq(t, c, 2); got != "EOF" {
		t.Fatalf("after the peer's Close: %q", got)
	}
	if err := c.Close(); err != nil {
		t.Errorf("Close after the peer's FIN: %v", err)
	}
	c, _ = pair(t)
	c.CloseWrite()
	if err := c.Close(); err != nil {
		t.Errorf("Close after CloseWrite: %v", err)
	}
	c, p = pair(t)
	resetBy(t, c, p)
	if err := c.Close(); err != nil {
		t.Errorf("Close after RST: %v", err)
	}
	c, _ = pair(t)
	go c.Read(make([]byte, 4))
	time.Sleep(10 * time.Millisecond)
	if err := c.Close(); err != nil {
		t.Errorf("Close with a blocked Read: %v", err)
	}
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	go ln.Accept()
	time.Sleep(10 * time.Millisecond)
	if err := ln.Close(); err != nil {
		t.Errorf("listener Close with a blocked Accept: %v", err)
	}
}

// TestAddrs (D18, TrustedCode/net.lean model.anyTCPAddr, conn.LocalAddr,
// conn.RemoteAddr, TCPListener.Addr). A connection's LocalAddr and
// RemoteAddr, and a listener's Addr, are non-nil *TCPAddr, the same pointer
// at every call, unchanged after a reset and after Close (both ends: the
// dialer's and the acceptor's). A zero TCPConn's are nil; a zero
// TCPListener's Addr panics (a nil fd). Measured.
func TestAddrs(t *testing.T) {
	t.Parallel()
	check := func(what string, c net.Conn) (l, r net.Addr) {
		t.Helper()
		l, r = c.LocalAddr(), c.RemoteAddr()
		for _, a := range []net.Addr{l, r} {
			if ta, ok := a.(*net.TCPAddr); !ok || ta == nil {
				t.Fatalf("%s: %T %v; want a non-nil *TCPAddr", what, a, a)
			}
		}
		if c.LocalAddr() != l || c.RemoteAddr() != r {
			t.Errorf("%s: a second call returned other pointers", what)
		}
		return l, r
	}
	d, a := pair(t)
	dl, dr := check("dialer", d)
	al, ar := check("acceptor", a)
	resetBy(t, d, a)
	if d.LocalAddr() != dl || d.RemoteAddr() != dr {
		t.Errorf("dialer's addresses changed after a reset")
	}
	d.Close()
	if d.LocalAddr() != dl || d.RemoteAddr() != dr || a.LocalAddr() != al || a.RemoteAddr() != ar {
		t.Errorf("addresses changed after Close")
	}
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	la := ln.Addr()
	if ta, ok := la.(*net.TCPAddr); !ok || ta == nil || ln.Addr() != la {
		t.Fatalf("listener Addr %T %v; want the same non-nil *TCPAddr", la, la)
	}
	ln.Close()
	if ln.Addr() != la {
		t.Errorf("listener Addr changed after Close")
	}
	var z net.TCPConn
	if z.LocalAddr() != nil || z.RemoteAddr() != nil {
		t.Errorf("zero TCPConn's addresses: %v %v; want nil", z.LocalAddr(), z.RemoteAddr())
	}
	func() {
		defer func() {
			if recover() == nil {
				t.Errorf("zero TCPListener's Addr did not panic")
			}
		}()
		var zl net.TCPListener
		zl.Addr()
	}()
}

// TestDialTimeoutAccepted (D16, D19; Impl.lean DialStep's last disjunct,
// NetConn.abandoned; TrustedCode/net.lean DialTimeout.impl). A DialTimeout
// that fails can leave a connection that the listener's Accept returns: Go's
// connect waits for the socket to become writable under the dial's deadline
// and, when it fires, closes the socket and returns a timeout even if the
// kernel finished the handshake meanwhile, so the listener's kernel has
// queued the connection. Its acceptor reads io.EOF (the dialer's close sent a
// FIN, nothing was written) or an error, never data. Every failure's Err is
// a timeout (Timeout() true: net's errTimeout, or os.ErrDeadlineExceeded) or
// an *os.SyscallError, and both timeout shapes occur (measured 255 and 745 of
// 1000): netFD.connect's WaitWrite returns poll.ErrDeadlineExceeded under the
// write deadline it set to the dial's deadline when the context's timer has
// not fired yet (fd_unix.go, connect), and mapErr(ctx.Err()) = errTimeout
// once it has (connect's ctxDone case, dialSerial). DialTimeouts of 1-60 us on loopback, the dialer
// writing one byte on each success; repeated until a failed dial's
// connection has been accepted. (Ported from dsverify-lab
// harness/netsem/dial_timeout_accepted.go.) Measured.
func TestDialTimeoutAccepted(t *testing.T) {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	addr := ln.Addr().String()
	var mu sync.Mutex
	got := map[string]int{}
	var wg sync.WaitGroup
	done := make(chan struct{})
	go func() {
		defer close(done)
		for {
			c, err := ln.Accept()
			if err != nil {
				return
			}
			wg.Add(1)
			go func() {
				defer wg.Done()
				defer c.Close()
				b := make([]byte, 2)
				c.SetReadDeadline(time.Now().Add(2 * time.Second))
				n, err := c.Read(b)
				k := "data " + string(b[:n])
				if n == 0 {
					k = name(err)
				}
				mu.Lock()
				got[k]++
				mu.Unlock()
			}()
		}
	}()
	ok, fail, dlx, ito := 0, 0, 0, 0
	for round := 0; round < 10; round++ {
		for i := 0; i < 1000; i++ {
			c, err := net.DialTimeout("tcp", addr, time.Duration(1+i%60)*time.Microsecond)
			if err != nil {
				fail++
				oe := opErr(t, "DialTimeout", err)
				_, se := oe.Err.(*os.SyscallError)
				switch {
				case errors.Is(err, os.ErrDeadlineExceeded):
					dlx++
				case oe.Timeout() && oe.Err.Error() == "i/o timeout":
					ito++
				case !se:
					t.Errorf("DialTimeout: Err %T %v; want a timeout or an *os.SyscallError", oe.Err, oe.Err)
				}
				continue
			}
			ok++
			c.Write([]byte{'D'})
			c.Close()
		}
		// let the acceptors read what is queued
		waitFor(t, "the accepted connections to be read", func() bool {
			mu.Lock()
			defer mu.Unlock()
			n := 0
			for _, v := range got {
				n += v
			}
			return n >= ok
		})
		time.Sleep(50 * time.Millisecond)
		mu.Lock()
		n := 0
		for _, v := range got {
			n += v
		}
		mu.Unlock()
		if n > ok && dlx > 0 && ito > 0 {
			break
		}
	}
	ln.Close()
	<-done
	wg.Wait()
	accepted := 0
	for k, v := range got {
		accepted += v
		if k != "data D" && len(k) > 4 && k[:5] == "data " {
			t.Errorf("an accepted connection carried %q, which no dialer wrote", k)
		}
	}
	t.Logf("%d DialTimeouts ok, %d failed (%d os.ErrDeadlineExceeded, %d errTimeout); accepted %d: %v",
		ok, fail, dlx, ito, accepted, got)
	if got["data D"] != ok {
		t.Errorf("accepted with data: %d; successful dials: %d", got["data D"], ok)
	}
	if accepted <= ok {
		t.Errorf("no failed DialTimeout's connection was accepted (%d accepted, %d ok)", accepted, ok)
	}
	if dlx == 0 || ito == 0 {
		t.Errorf("a timeout shape not seen: %d os.ErrDeadlineExceeded, %d errTimeout", dlx, ito)
	}
}

// TestWildcardListen (D21, Impl.lean ListenAt, wildPort; extends
// TestAddressAliases). Each wildcard spelling, ":P", "0.0.0.0:P" and
// "[::]:P", listens: its Addr is "[::]:P" (Go's dual-stack wildcard); it
// accepts a Dial of "127.0.0.1:P"; and with it open, Listen of "127.0.0.1:P"
// fails (EADDRINUSE). Measured.
func TestWildcardListen(t *testing.T) {
	t.Parallel()
	for _, h := range []string{"", "0.0.0.0", "[::]"} {
		probe, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatal(err)
		}
		p := strconv.Itoa(probe.Addr().(*net.TCPAddr).Port)
		probe.Close()
		forkMu.RLock()
		w, err := net.Listen("tcp", h+":"+p)
		forkMu.RUnlock()
		if err != nil {
			t.Logf("Listen(%q): %v (port taken meanwhile); skipped", h+":"+p, err)
			continue
		}
		if got := w.Addr().String(); got != "[::]:"+p {
			t.Errorf("Listen(%q).Addr() = %q; want [::]:%s", h+":"+p, got, p)
		}
		c, err := net.Dial("tcp", "127.0.0.1:"+p)
		if err != nil {
			t.Errorf("Dial(127.0.0.1:%s) with %q listened: %v", p, h+":"+p, err)
		} else {
			a, err := w.Accept()
			if err != nil {
				t.Errorf("Accept: %v", err)
			} else {
				a.Close()
			}
			c.Close()
		}
		if l2, err := net.Listen("tcp", "127.0.0.1:"+p); err == nil {
			l2.Close()
			t.Errorf("Listen(127.0.0.1:%s) with %q open succeeded; want EADDRINUSE", p, h+":"+p)
		} else if name(err) != "EADDRINUSE" {
			t.Errorf("Listen(127.0.0.1:%s) with %q open: %v; want EADDRINUSE", p, h+":"+p, err)
		}
		w.Close()
	}
}
