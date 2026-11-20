// Package tcpwriteloop measures the corners of Go's Write loop that the TCP
// semantics v3.1 models as a loop of steps (GooseLang/Ext/Net/Impl.lean, D2,
// D15; Net/TrustedCode/net.lean, model.writeLoop), for the v3.1 review
// (notes/axiom-review/tcp-semantics.md, "v3.1 (2026-11-15)"). Tests only: none
// is a counterexample; each records what Go and Linux do where a mismatch with
// the model could hide, and says which model behavior covers it.
//
// Every test uses its own fixed loopback port (7181-7186: canonical plan
// addresses outside the ephemeral range, D13/D20), so that a run built with
// the conformance tracer (examples/net/conform) can be checked against the
// model as it is.
package tcpwriteloop

import (
	"bytes"
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

// Size is larger than loopback's socket buffers hold (tcp_wmem max 4 MiB,
// tcp_rmem max 6 MiB here), so a Write of Size blocks while the peer does not
// read (the measured Writes block after about 5.4 MB). $NET_WL_SIZE
// overrides it (12 MiB for a traced run: the Lean replay overflows its stack
// on a 32 MiB step).
var Size = func() int {
	if v, err := strconv.Atoi(os.Getenv("NET_WL_SIZE")); err == nil && v > 0 {
		return v
	}
	return 32 << 20
}()

// iters returns n, or $NET_WL_ITERS if set (1 for a traced run: the
// conformance tracer records every byte).
func iters(n int) int {
	if v, err := strconv.Atoi(os.Getenv("NET_WL_ITERS")); err == nil && v > 0 {
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

// readAll reads a to its end, returning what it read and the error that
// ended it (nil for EOF). A loop of Reads, not io.Copy, whose
// (*TCPConn).WriteTo the model does not have.
func readAll(a net.Conn) ([]byte, error) {
	var buf bytes.Buffer
	chunk := make([]byte, 64<<10)
	for {
		k, err := a.Read(chunk)
		buf.Write(chunk[:k])
		if err == io.EOF {
			return buf.Bytes(), nil
		}
		if err != nil {
			return buf.Bytes(), err
		}
	}
}

// fill returns n bytes of b.
func fill(b byte, n int) []byte { return bytes.Repeat([]byte{b}, n) }

// TestConcurrentWritesSerialized: two goroutines Write 8 MiB each (all 'a',
// all 'b') on one end at once, the peer reading slowly. Go's writeLock
// (poll.FD.Write) serializes them: the peer reads all of one, then all of
// the other, never an interleaving. The model may interleave the two Writes'
// steps (a precision loss, sound: Go's order is one of the model's).
func TestConcurrentWritesSerialized(t *testing.T) {
	const n = 8 << 20
	for i := 0; i < iters(10); i++ {
		c, a, l := pair(t, "127.0.0.1:7181")
		var wg sync.WaitGroup
		errs := make([]error, 2)
		counts := make([]int, 2)
		for j, b := range []byte{'a', 'b'} {
			wg.Add(1)
			go func(j int, b byte) {
				defer wg.Done()
				counts[j], errs[j] = c.Write(fill(b, n))
			}(j, b)
		}
		var got []byte
		done := make(chan struct{})
		go func() {
			var buf bytes.Buffer
			chunk := make([]byte, 64<<10)
			for buf.Len() < 2*n {
				k, err := a.Read(chunk)
				buf.Write(chunk[:k])
				if err != nil {
					break
				}
				time.Sleep(100 * time.Microsecond)
			}
			got = buf.Bytes()
			close(done)
		}()
		wg.Wait()
		<-done
		for j := range errs {
			if errs[j] != nil || counts[j] != n {
				t.Fatalf("run %d: Write %d = (%d, %v)", i, j, counts[j], errs[j])
			}
		}
		if len(got) != 2*n {
			t.Fatalf("run %d: read %d bytes", i, len(got))
		}
		switches := 0
		for k := 1; k < len(got); k++ {
			if got[k] != got[k-1] {
				switches++
			}
		}
		if switches != 1 {
			t.Errorf("run %d: the two Writes interleaved (%d switches)", i, switches)
		}
		c.Close()
		a.Close()
		l.Close()
	}
}

// TestCloseDuringWrite: a Write of Size blocks; the peer reads 1 MiB; another
// goroutine Closes the writer's end. Measured: the Write returns (n, err)
// with 0 < n < Size and err an *OpError around poll.ErrNetClosing
// (errors.Is net.ErrClosed); Close returns nil, and only once the Write has
// made its last system call (poll.FD.Close waits on csema, which the Write's
// writeUnlock releases, deferred in poll.FD.Write: so Close may return a few
// microseconds before the Write's caller resumes; logged, not checked); the
// peer reads exactly n bytes, then EOF: the failing step appended nothing.
// The model: progress steps appending n, the Close step, a failing step
// (closed); the Close step may be placed anywhere in Close's interval, which
// contains the Write's last write(2).
func TestCloseDuringWrite(t *testing.T) {
	for i := 0; i < iters(10); i++ {
		c, a, l := pair(t, "127.0.0.1:7182")
		type res struct {
			n   int
			err error
			at  time.Time
		}
		wr := make(chan res, 1)
		go func() {
			n, err := c.Write(make([]byte, Size))
			wr <- res{n, err, time.Now()}
		}()
		head := make([]byte, 1<<20)
		if _, err := io.ReadFull(a, head); err != nil {
			t.Fatal(err)
		}
		cerr := c.Close()
		closedAt := time.Now()
		w := <-wr
		rest, rerr := readAll(a)
		if cerr != nil {
			t.Errorf("run %d: Close = %v", i, cerr)
		}
		if !errors.Is(w.err, net.ErrClosed) || w.n <= 0 || w.n >= Size {
			t.Errorf("run %d: Write = (%d, %v); want 0 < n < Size, ErrClosed", i, w.n, w.err)
		}
		if rerr != nil || len(head)+len(rest) != w.n {
			t.Errorf("run %d: the peer read %d bytes (%v); the Write returned %d",
				i, len(head)+len(rest), rerr, w.n)
		}
		if i == 0 {
			t.Logf("Write = (%d, %v); Close = %v, returned %v after the Write's caller resumed; the peer read %d, then EOF",
				w.n, w.err, cerr, closedAt.Sub(w.at), len(head)+len(rest))
		}
		a.Close()
		l.Close()
	}
}

// TestTwoWritesAndClose: a Write of Size blocks holding the write lock; a
// second Write of Size waits for the lock; Close. Measured: the first returns
// (n, ErrClosed) with 0 < n < Size, the second (0, ErrClosed), and the peer
// reads exactly n bytes, then EOF. The model: the second Write's one step is
// on the closed end.
func TestTwoWritesAndClose(t *testing.T) {
	for i := 0; i < iters(10); i++ {
		c, a, l := pair(t, "127.0.0.1:7183")
		type res struct {
			n   int
			err error
		}
		w1, w2 := make(chan res, 1), make(chan res, 1)
		go func() {
			n, err := c.Write(fill('a', Size))
			w1 <- res{n, err}
		}()
		head := make([]byte, 1<<20)
		if _, err := io.ReadFull(a, head); err != nil {
			t.Fatal(err)
		}
		go func() {
			n, err := c.Write(fill('b', Size))
			w2 <- res{n, err}
		}()
		time.Sleep(20 * time.Millisecond) // the second Write waits for the lock
		c.Close()
		r1, r2 := <-w1, <-w2
		rest, rerr := readAll(a)
		got := append(head, rest...)
		if !errors.Is(r1.err, net.ErrClosed) || r1.n <= 0 || r1.n >= Size {
			t.Errorf("run %d: first Write = (%d, %v)", i, r1.n, r1.err)
		}
		if !errors.Is(r2.err, net.ErrClosed) || r2.n != 0 {
			t.Errorf("run %d: second Write = (%d, %v); want (0, ErrClosed)", i, r2.n, r2.err)
		}
		if rerr != nil || len(got) != r1.n || bytes.IndexByte(got, 'b') >= 0 {
			t.Errorf("run %d: the peer read %d bytes (%v); want %d of the first Write's",
				i, len(got), rerr, r1.n)
		}
		if i == 0 {
			t.Logf("first Write = (%d, %v); second = (%d, %v); the peer read %d, then EOF",
				r1.n, r1.err, r2.n, r2.err, len(got))
		}
		a.Close()
		l.Close()
	}
}

// TestReadDeadlineDuringWrite: a Write of Size blocks; another goroutine sets
// the writer's read deadline to now (an expired deadline of the other kind);
// the peer then reads everything. Measured: the Write returns (Size, nil):
// a read deadline never times a Write out. The model: SetReadDeadline (kind
// 1) leaves wdl, so no step of the Write can time out (WriteOutcome's
// timeout clauses need st.wdl = true): the model's one outcome, Go's.
func TestReadDeadlineDuringWrite(t *testing.T) {
	for i := 0; i < iters(10); i++ {
		c, a, l := pair(t, "127.0.0.1:7184")
		type res struct {
			n   int
			err error
		}
		wr := make(chan res, 1)
		go func() {
			n, err := c.Write(make([]byte, Size))
			wr <- res{n, err}
		}()
		head := make([]byte, 1<<20)
		if _, err := io.ReadFull(a, head); err != nil {
			t.Fatal(err)
		}
		if err := c.SetReadDeadline(time.Now()); err != nil {
			t.Fatal(err)
		}
		time.Sleep(20 * time.Millisecond)
		rest := make([]byte, Size-len(head))
		if _, err := io.ReadFull(a, rest); err != nil {
			t.Fatal(err)
		}
		w := <-wr
		if w.err != nil || w.n != Size {
			t.Errorf("run %d: Write = (%d, %v); want (Size, nil)", i, w.n, w.err)
		}
		c.Close()
		a.Close()
		l.Close()
	}
}

// TestDeadlineSetThenCleared: a Write of Size blocks; another goroutine sets
// the write deadline to now and at once clears it (SetWriteDeadline of the
// zero time); the peer then reads everything. Go: the Write times out
// (n, ErrDeadlineExceeded) if the poller ran it between the two calls, else
// it returns (Size, nil). The model allows both (wdl is true between the two
// SetDeadline steps, false after). Counted, not required.
func TestDeadlineSetThenCleared(t *testing.T) {
	timeouts, oks := 0, 0
	for i := 0; i < iters(20); i++ {
		c, a, l := pair(t, "127.0.0.1:7185")
		type res struct {
			n   int
			err error
		}
		wr := make(chan res, 1)
		go func() {
			n, err := c.Write(make([]byte, Size))
			wr <- res{n, err}
		}()
		head := make([]byte, 1<<20)
		if _, err := io.ReadFull(a, head); err != nil {
			t.Fatal(err)
		}
		c.SetWriteDeadline(time.Now())
		c.SetWriteDeadline(time.Time{})
		done := make(chan []byte)
		go func() {
			b, _ := readAll(a)
			done <- b
		}()
		w := <-wr
		c.Close()
		rest := <-done
		switch {
		case w.err == nil && w.n == Size:
			oks++
		case errors.Is(w.err, os.ErrDeadlineExceeded) && w.n > 0 && w.n < Size:
			timeouts++
		default:
			t.Errorf("run %d: Write = (%d, %v)", i, w.n, w.err)
		}
		if len(head)+len(rest) != w.n {
			t.Errorf("run %d: the peer read %d; the Write returned %d", i, len(head)+len(rest), w.n)
		}
		a.Close()
		l.Close()
	}
	t.Logf("%d timed out, %d wrote everything", timeouts, oks)
}

// TestCloseWriteDuringWrite: a Write of Size blocks; the peer reads 1 MiB;
// another goroutine calls CloseWrite on the writer's end. Measured: the
// Write returns (n, err), 0 < n < Size, err an *OpError around an
// *os.SyscallError("write", EPIPE); the peer reads exactly n bytes, then
// EOF: the failing write(2) appended nothing. The model: steps appending n,
// CloseWrite shutting the direction (fin), a failing step (sys on fin).
func TestCloseWriteDuringWrite(t *testing.T) {
	for i := 0; i < iters(10); i++ {
		c, a, l := pair(t, "127.0.0.1:7186")
		type res struct {
			n   int
			err error
		}
		wr := make(chan res, 1)
		go func() {
			n, err := c.Write(make([]byte, Size))
			wr <- res{n, err}
		}()
		head := make([]byte, 1<<20)
		if _, err := io.ReadFull(a, head); err != nil {
			t.Fatal(err)
		}
		if err := c.(*net.TCPConn).CloseWrite(); err != nil {
			t.Fatal(err)
		}
		rest, rerr := readAll(a)
		w := <-wr
		var se *os.SyscallError
		if !errors.As(w.err, &se) || se.Syscall != "write" || se.Err != syscall.EPIPE ||
			w.n <= 0 || w.n >= Size {
			t.Errorf("run %d: Write = (%d, %v); want 0 < n < Size, write: EPIPE", i, w.n, w.err)
		}
		if rerr != nil || len(head)+len(rest) != w.n {
			t.Errorf("run %d: the peer read %d (%v); the Write returned %d", i, len(head)+len(rest), rerr, w.n)
		}
		if i == 0 {
			t.Logf("Write = (%d, %v); the peer read %d, then EOF", w.n, w.err, len(head)+len(rest))
		}
		c.Close()
		a.Close()
		l.Close()
	}
}
