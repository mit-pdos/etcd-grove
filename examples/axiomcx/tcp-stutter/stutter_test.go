// Package tcpstutter measures what the TCP semantics v3.2 changed
// (GooseLang/Ext/Tcp/Impl.lean, D22; NetTcp/TrustedCode/net.lean), for the
// v3.2 review (notes/axiom-review/tcp-semantics.md, "v3.2 (2026-11-15)").
// Tests only: none is a counterexample.
//
//   - The waits are stutters: a Read, an Accept, a Write that blocks and then
//     returns (bytes, a connection, progress, or a failure: a deadline, a
//     close, the peer's reset). v3.1 had a wait outcome for each (ReadRes.wait,
//     AcceptStep's waiting clause, a Write step counting nothing); v3.2 has
//     none, so the real call's return must be an outcome rule of the state it
//     returns in. Every test here uses its own fixed loopback port
//     (7161-7169: canonical plan addresses outside the ephemeral range,
//     D13/D20), so that a run built with the conformance tracer
//     (examples/net/conform) can be checked against the model as it is.
//   - The zero values: net.lean's models return the bare syscall.EINVAL for a
//     zero TCPConn or TCPListener (model.einval) before calling the extension.
//     TestZeroValuesEvery covers every modeled method (examples/net/semantics'
//     TestZeroValues covers seven), TestZeroedConn a live connection's struct
//     overwritten by the zero value, TestNilReceivers the nil pointers (where
//     the models are stuck: a nil load; sound whatever Go does).
package tcpstutter

import (
	"bytes"
	"errors"
	"io"
	"net"
	"os"
	"runtime"
	"strconv"
	"syscall"
	"testing"
	"time"
)

// Size is more than loopback's socket buffers hold (tcp_wmem max 4 MiB,
// tcp_rmem max 6 MiB), so a Write of Size blocks while the peer does not
// read. 12 MiB: a traced run's steps must fit the Lean replay (the v3.1
// review's M3).
var Size = func() int {
	if v, err := strconv.Atoi(os.Getenv("NETTCP_ST_SIZE")); err == nil && v > 0 {
		return v
	}
	return 12 << 20
}()

// iters returns n, or $NETTCP_ST_ITERS if set (1 for a traced run).
func iters(n int) int {
	if v, err := strconv.Atoi(os.Getenv("NETTCP_ST_ITERS")); err == nil && v > 0 {
		return v
	}
	return n
}

// pair listens at addr, dials it and accepts: the dialer's end and the
// acceptor's.
func pair(t *testing.T, addr string) (c, a net.Conn, l net.Listener) {
	t.Helper()
	l, err := net.Listen("tcp", addr)
	if err != nil {
		t.Fatal(err)
	}
	c, err = net.Dial("tcp", addr)
	if err != nil {
		l.Close()
		t.Fatal(err)
	}
	a, err = l.Accept()
	if err != nil {
		c.Close()
		l.Close()
		t.Fatal(err)
	}
	return c, a, l
}

func closeAll(cs ...io.Closer) {
	for _, c := range cs {
		c.Close()
	}
}

// readN reads a until it has n bytes or an error.
func readN(a net.Conn, n int) ([]byte, error) {
	var buf bytes.Buffer
	chunk := make([]byte, 64<<10)
	for buf.Len() < n {
		k, err := a.Read(chunk)
		buf.Write(chunk[:k])
		if err != nil {
			return buf.Bytes(), err
		}
	}
	return buf.Bytes(), nil
}

// isClosed: an *OpError around poll.ErrNetClosing (net.lean's closedErr).
func isClosed(err error) bool {
	var oe *net.OpError
	return errors.As(err, &oe) && errors.Is(err, net.ErrClosed)
}

// isTimeout: an *OpError around poll.ErrDeadlineExceeded (net.lean's
// deadlineErr).
func isTimeout(err error) bool {
	var oe *net.OpError
	return errors.As(err, &oe) && errors.Is(err, os.ErrDeadlineExceeded)
}

// isSys: an *OpError around an *os.SyscallError of a nonzero Errno (net.lean's
// sysErr).
func isSys(err error) bool {
	var oe *net.OpError
	var se *os.SyscallError
	var en syscall.Errno
	return errors.As(err, &oe) && errors.As(oe.Err, &se) && errors.As(se.Err, &en) && en != 0
}

// TestReadBlocksThenBytes (D1, D22): a Read of 64 bytes at an end whose
// incoming direction is open and empty blocks (the model: stutters; no outcome
// rule but a break or, with a deadline, a timeout); the peer Writes 5 bytes
// after 100 ms; the Read returns 1..5 of them, nil (the model: the bytes
// rule, once the Write's step has appended them). Then the peer's CloseWrite:
// the rest, then EOF.
func TestReadBlocksThenBytes(t *testing.T) {
	for i := 0; i < iters(20); i++ {
		c, a, l := pair(t, "127.0.0.1:7161")
		go func() {
			time.Sleep(100 * time.Millisecond)
			c.Write([]byte("hello"))
			c.(*net.TCPConn).CloseWrite()
		}()
		start := time.Now()
		buf := make([]byte, 64)
		n, err := a.Read(buf)
		if err != nil || n < 1 || n > 5 || !bytes.Equal(buf[:n], []byte("hello")[:n]) {
			t.Fatalf("run %d: Read = (%d %q, %v)", i, n, buf[:n], err)
		}
		if d := time.Since(start); d < 90*time.Millisecond {
			t.Fatalf("run %d: the Read did not block (%v)", i, d)
		}
		rest, err := io.ReadAll(a)
		if err != nil || string(buf[:n])+string(rest) != "hello" {
			t.Fatalf("run %d: rest %q, %v", i, rest, err)
		}
		closeAll(c, a, l)
	}
}

// TestAcceptBlocksThenAccepts (D7, D22): an Accept of an open listener with
// nothing pending blocks (the model: stutters; its outcome rules are a sys
// failure and a pending connection); a Dial after 100 ms; the Accept returns
// that connection (the model: the Dial's step, then the Accept's).
func TestAcceptBlocksThenAccepts(t *testing.T) {
	for i := 0; i < iters(20); i++ {
		l, err := net.Listen("tcp", "127.0.0.1:7162")
		if err != nil {
			t.Fatal(err)
		}
		dialed := make(chan net.Conn, 1)
		go func() {
			time.Sleep(100 * time.Millisecond)
			c, err := net.Dial("tcp", "127.0.0.1:7162")
			if err != nil {
				t.Error(err)
			}
			dialed <- c
		}()
		start := time.Now()
		a, err := l.Accept()
		if err != nil {
			t.Fatalf("run %d: Accept: %v", i, err)
		}
		if d := time.Since(start); d < 90*time.Millisecond {
			t.Fatalf("run %d: the Accept did not block (%v)", i, d)
		}
		c := <-dialed
		if c == nil {
			t.FailNow()
		}
		c.Write([]byte("x"))
		if b, err := readN(a, 1); err != nil || string(b) != "x" {
			t.Fatalf("run %d: %q %v", i, b, err)
		}
		closeAll(c, a, l)
	}
}

// TestWriteBlocksForSpace (D2, D15, D22): a Write of Size while the peer does
// not read fills the buffers and blocks (EAGAIN, waitWrite: the model
// stutters, its steps so far having counted what write(2) took); the peer
// starts reading after 200 ms; the Write returns (Size, nil), every byte
// read in order (the model: more steps, each counting at least one byte).
func TestWriteBlocksForSpace(t *testing.T) {
	for i := 0; i < iters(10); i++ {
		c, a, l := pair(t, "127.0.0.1:7163")
		data := bytes.Repeat([]byte("0123456789abcdef"), Size/16)
		type res struct {
			n   int
			err error
			d   time.Duration
		}
		done := make(chan res, 1)
		start := time.Now()
		go func() {
			n, err := c.Write(data)
			done <- res{n, err, time.Since(start)}
		}()
		time.Sleep(200 * time.Millisecond)
		got, rerr := readN(a, len(data))
		r := <-done
		if r.err != nil || r.n != len(data) {
			t.Fatalf("run %d: Write = (%d, %v)", i, r.n, r.err)
		}
		if r.d < 190*time.Millisecond {
			t.Fatalf("run %d: the Write did not block (%v)", i, r.d)
		}
		if rerr != nil || !bytes.Equal(got, data) {
			t.Fatalf("run %d: read %d bytes, %v", i, len(got), rerr)
		}
		closeAll(c, a, l)
	}
}

// TestAcceptBlockedThenClose (D7, D9, D22): an Accept blocked on an open
// listener; the listener's Close after 100 ms; the Accept returns an *OpError
// around ErrNetClosing (the model: the stutter, LisClose's step, then
// Accept's only rule on a closed listener, closed), and Close nil.
func TestAcceptBlockedThenClose(t *testing.T) {
	for i := 0; i < iters(20); i++ {
		l, err := net.Listen("tcp", "127.0.0.1:7164")
		if err != nil {
			t.Fatal(err)
		}
		cerr := make(chan error, 1)
		go func() {
			time.Sleep(100 * time.Millisecond)
			cerr <- l.Close()
		}()
		c, err := l.Accept()
		if c != nil || !isClosed(err) {
			t.Fatalf("run %d: Accept = (%v, %T %v)", i, c, err, err)
		}
		if err := <-cerr; err != nil {
			t.Fatalf("run %d: Close = %v", i, err)
		}
	}
}

// TestReadBlockedThenDeadline (D1, D5, D22): a Read blocked (open, empty, no
// deadline: the model has only the stutter and a break); another goroutine
// sets a read deadline 50 ms ahead; the Read times out (the model: the
// SetDeadline step, then the timeout rule, rdl set); the connection is
// unchanged: bytes written after it are read.
func TestReadBlockedThenDeadline(t *testing.T) {
	for i := 0; i < iters(20); i++ {
		c, a, l := pair(t, "127.0.0.1:7165")
		go func() {
			time.Sleep(50 * time.Millisecond)
			a.SetReadDeadline(time.Now().Add(50 * time.Millisecond))
		}()
		n, err := a.Read(make([]byte, 8))
		if n != 0 || !isTimeout(err) {
			t.Fatalf("run %d: Read = (%d, %T %v)", i, n, err, err)
		}
		a.SetReadDeadline(time.Time{})
		c.Write([]byte("ok"))
		if b, err := readN(a, 2); err != nil || string(b) != "ok" {
			t.Fatalf("run %d: %q %v", i, b, err)
		}
		closeAll(c, a, l)
	}
}

// TestReadBlockedThenClose (D1, D3, D22): a Read blocked; the same end's
// Close from another goroutine; the Read returns an *OpError around
// ErrNetClosing (the model: the Close step, then the Read's closed rule);
// the peer reads EOF.
func TestReadBlockedThenClose(t *testing.T) {
	for i := 0; i < iters(20); i++ {
		c, a, l := pair(t, "127.0.0.1:7166")
		go func() {
			time.Sleep(50 * time.Millisecond)
			a.Close()
		}()
		n, err := a.Read(make([]byte, 8))
		if n != 0 || !isClosed(err) {
			t.Fatalf("run %d: Read = (%d, %T %v)", i, n, err, err)
		}
		if b, err := io.ReadAll(c); err != nil || len(b) != 0 {
			t.Fatalf("run %d: the peer read %q, %v", i, b, err)
		}
		closeAll(c, l)
	}
}

// TestEmptyWriteOnFullBuffer (D2, D22): the send buffer filled (a Write with
// a write deadline that times out after writing a part); the deadline
// cleared; then an empty Write: it returns (0, nil) at once (write(2) of no
// bytes on a full buffer returns 0: tcp_sendmsg_locked's loop does not run).
// The model: the empty rs's non-failing step, k = 0 (the one k = 0 success
// v3.2 keeps).
func TestEmptyWriteOnFullBuffer(t *testing.T) {
	for i := 0; i < iters(20); i++ {
		c, a, l := pair(t, "127.0.0.1:7167")
		data := bytes.Repeat([]byte("z"), Size)
		c.SetWriteDeadline(time.Now().Add(200 * time.Millisecond))
		n, err := c.Write(data)
		if !isTimeout(err) || n <= 0 || n >= len(data) {
			t.Fatalf("run %d: filling Write = (%d, %T %v)", i, n, err, err)
		}
		c.SetWriteDeadline(time.Time{})
		start := time.Now()
		m, err := c.Write(nil)
		if m != 0 || err != nil {
			t.Fatalf("run %d: empty Write = (%d, %T %v)", i, m, err, err)
		}
		if d := time.Since(start); d > 50*time.Millisecond {
			t.Fatalf("run %d: the empty Write blocked (%v)", i, d)
		}
		got, err := readN(a, n)
		if err != nil || !bytes.Equal(got, data[:n]) {
			t.Fatalf("run %d: read %d, %v", i, len(got), err)
		}
		closeAll(c, a, l)
	}
}

// TestWriteBlockedPeerCloses (D2, D3, D22): a Write of Size blocked (the peer
// reads nothing); the peer Closes with bytes unread (Linux resets the
// connection); the Write returns (n, sys) with 0 < n < Size, an
// *os.SyscallError (ECONNRESET or EPIPE) (the model: steps counting n, the
// peer's Close step shutting its own direction, then a failing sys step of
// the writer's open direction, cutting it).
func TestWriteBlockedPeerCloses(t *testing.T) {
	for i := 0; i < iters(20); i++ {
		c, a, l := pair(t, "127.0.0.1:7168")
		go func() {
			time.Sleep(100 * time.Millisecond)
			a.Close()
		}()
		n, err := c.Write(bytes.Repeat([]byte("y"), Size))
		if n <= 0 || n >= Size || !isSys(err) {
			t.Fatalf("run %d: Write = (%d, %T %v)", i, n, err, err)
		}
		t.Logf("run %d: Write = (%d, %v)", i, n, err)
		closeAll(c, l)
	}
}

// TestZeroValuesEvery (net.lean's model.einval, D22): every method the models
// cover, on a zero TCPConn and a zero TCPListener, directly and through the
// interfaces: the bare syscall.EINVAL (dynamic type syscall.Errno, value
// 0x16, not an *OpError), before anything else (an empty Read and an empty
// Write too, a second Close too, a zero time too); LocalAddr and RemoteAddr
// nil; Accept a nil Conn; the listener's Addr a nil dereference (the model:
// Panic, stuck).
func TestZeroValuesEvery(t *testing.T) {
	var c net.TCPConn
	var l net.TCPListener
	var ci net.Conn = &c
	var li net.Listener = &l
	check := func(op string, err error) {
		t.Helper()
		if err != syscall.EINVAL {
			t.Errorf("%s: %T %v; want the bare syscall.EINVAL", op, err, err)
		}
		if en, ok := err.(syscall.Errno); !ok || uintptr(en) != 22 {
			t.Errorf("%s: %T %v; want syscall.Errno(22)", op, err, err)
		}
	}
	for _, n := range []int{0, 1} {
		k, err := c.Read(make([]byte, n))
		if k != 0 {
			t.Errorf("Read(%d) = %d", n, k)
		}
		check("Read "+strconv.Itoa(n), err)
		k, err = c.Write(make([]byte, n))
		if k != 0 {
			t.Errorf("Write(%d) = %d", n, k)
		}
		check("Write "+strconv.Itoa(n), err)
		k, err = ci.Read(make([]byte, n))
		check("Conn.Read "+strconv.Itoa(n), err)
		k, err = ci.Write(make([]byte, n))
		check("Conn.Write "+strconv.Itoa(n), err)
	}
	check("Close", c.Close())
	check("Close again", c.Close())
	check("Conn.Close", ci.Close())
	check("CloseWrite", c.CloseWrite())
	for _, tm := range []time.Time{{}, time.Now()} {
		check("SetDeadline", c.SetDeadline(tm))
		check("SetReadDeadline", c.SetReadDeadline(tm))
		check("SetWriteDeadline", c.SetWriteDeadline(tm))
	}
	if c.LocalAddr() != nil || c.RemoteAddr() != nil {
		t.Errorf("addresses %v %v; want nil", c.LocalAddr(), c.RemoteAddr())
	}
	ac, err := l.Accept()
	if ac != nil {
		t.Errorf("Accept's Conn %v; want nil", ac)
	}
	check("Accept", err)
	ac, err = li.Accept()
	if ac != nil {
		t.Errorf("Listener.Accept's Conn %v; want nil", ac)
	}
	check("Listener.Accept", err)
	check("listener Close", l.Close())
	check("listener Close again", li.Close())
	func() {
		defer func() {
			r := recover()
			if _, ok := r.(runtime.Error); !ok {
				t.Errorf("zero listener's Addr: recovered %v; want a runtime error", r)
			}
		}()
		_ = l.Addr()
		t.Errorf("zero listener's Addr returned")
	}()
}

// TestZeroedConn (net.lean's model.einval): a live connection's TCPConn
// overwritten by the zero value (`*tc = net.TCPConn{}`, which Go code outside
// net can write: the struct's only field is unexported, its value is not)
// answers EINVAL from then on; a copy taken before (`cp := *tc`) still names
// the socket, which stays open. The model: the struct store writes id 0 (the
// models' check then answers EINVAL), the copy keeps the id.
func TestZeroedConn(t *testing.T) {
	c, a, l := pair(t, "127.0.0.1:7169")
	defer closeAll(a, l)
	tc := c.(*net.TCPConn)
	cp := *tc
	*tc = net.TCPConn{}
	if _, err := tc.Write([]byte("x")); err != syscall.EINVAL {
		t.Fatalf("zeroed Write: %T %v", err, err)
	}
	if n, err := cp.Write([]byte("y")); n != 1 || err != nil {
		t.Fatalf("copy's Write = (%d, %v)", n, err)
	}
	if b, err := readN(a, 1); err != nil || string(b) != "y" {
		t.Fatalf("peer read %q, %v", b, err)
	}
	if err := cp.Close(); err != nil {
		t.Fatalf("copy's Close: %v", err)
	}
	if err := tc.Close(); err != syscall.EINVAL {
		t.Fatalf("zeroed Close: %T %v", err, err)
	}
}

// TestNilReceivers: nil pointers. Go: (*TCPListener)(nil)'s Accept and
// Close return EINVAL (l.ok() checks l != nil); (*TCPConn)(nil)'s promoted
// methods dereference nil (Go computes &c.conn: a runtime error) except where
// noted by the log. The models load the id through the pointer: a nil load,
// stuck (Perennial's GoLoad of a null pointer: no heap cell), so a program
// that calls one has no proof: sound whatever Go does. Logged, not checked.
func TestNilReceivers(t *testing.T) {
	try := func(name string, f func() error) {
		defer func() {
			if r := recover(); r != nil {
				t.Logf("%s: panics: %v", name, r)
			}
		}()
		t.Logf("%s: returns %T %v", name, f(), f())
	}
	var tc *net.TCPConn
	var tl *net.TCPListener
	try("(*TCPConn)(nil).Read", func() error { _, err := tc.Read(nil); return err })
	try("(*TCPConn)(nil).Close", func() error { return tc.Close() })
	try("(*TCPConn)(nil).CloseWrite", func() error { return tc.CloseWrite() })
	try("(*TCPListener)(nil).Accept", func() error { _, err := tl.Accept(); return err })
	try("(*TCPListener)(nil).Close", func() error { return tl.Close() })
}
