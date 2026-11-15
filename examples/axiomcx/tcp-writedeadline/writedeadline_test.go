package tcpwritedeadline

import (
	"errors"
	"io"
	"net"
	"os"
	"testing"
	"time"
)

// panics runs f and returns what it panicked with (nil if it returned).
func panics(f func()) (r any) {
	defer func() { r = recover() }()
	f()
	return nil
}

// TestMainPanics: Main panics. One run per process: a panicking run leaves its
// sockets open (repeat with go test -count=1 in a loop, as repeat.sh does).
func TestMainPanics(t *testing.T) {
	if r := panics(Main); r == nil {
		t.Fatal("Main returned without panicking")
	} else {
		t.Logf("Main panicked: %v", r)
	}
}

// TestWriteDeadlineSetDuring: what Main's run looks like, measured. A Write of
// Size bytes blocks; the peer reads one byte; another goroutine sets the
// writer's deadline (to now; or to 100 ms from now, which expires while the
// Write blocks); the Write returns (n, err) with 0 < n < Size and err an
// *OpError whose Err is os.ErrDeadlineExceeded itself, Timeout() true; the
// peer then reads exactly n bytes (the first one included) before the
// writer's Close makes it read EOF.
func TestWriteDeadlineSetDuring(t *testing.T) {
	for _, mode := range []string{"now", "future"} {
		l, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatal(err)
		}
		c, err := net.Dial("tcp", l.Addr().String())
		if err != nil {
			t.Fatal(err)
		}
		a, err := l.Accept()
		if err != nil {
			t.Fatal(err)
		}
		read1 := make(chan error)
		go func() {
			b := make([]byte, 1)
			_, err := a.Read(b)
			switch mode {
			case "now":
				c.SetDeadline(time.Now())
			case "future":
				c.SetWriteDeadline(time.Now().Add(100 * time.Millisecond))
			}
			read1 <- err
		}()
		n, err := c.Write(make([]byte, Size))
		if err1 := <-read1; err1 != nil {
			t.Errorf("%s: first Read: %v", mode, err1)
		}
		var oe *net.OpError
		if !errors.As(err, &oe) || oe.Err != os.ErrDeadlineExceeded || !oe.Timeout() {
			t.Fatalf("%s: Write = (%d, %v); want a deadline error", mode, n, err)
		}
		if n <= 0 || n >= Size {
			t.Errorf("%s: Write wrote %d of %d bytes; want 0 < n < Size", mode, n, Size)
		}
		c.Close()
		r, cerr := io.Copy(io.Discard, a)
		if cerr != nil {
			t.Errorf("%s: Copy: %v", mode, cerr)
		}
		if 1+r != int64(n) {
			t.Errorf("%s: the peer read %d bytes; the Write returned %d", mode, 1+r, n)
		}
		t.Logf("%s: Write = (%d, %v), Err %T, Timeout %v; the peer read %d bytes, then EOF", mode,
			n, err, oe.Err, oe.Timeout(), 1+r)
		a.Close()
		l.Close()
	}
}

// TestListenOrders: D21's forced failure in both orders, for the three
// wildcard spellings (an attack that failed: every pair conflicts,
// EADDRINUSE).
func TestListenOrders(t *testing.T) {
	try := func(first, second string) {
		l1, err := net.Listen("tcp", first)
		if err != nil {
			t.Logf("Listen(%q): %v; skipped", first, err)
			return
		}
		defer l1.Close()
		l2, err := net.Listen("tcp", second)
		if err == nil {
			l2.Close()
			t.Errorf("Listen(%q) with %q open succeeded", second, first)
		}
	}
	const p = "7196"
	ws := []string{":" + p, "0.0.0.0:" + p, "[::]:" + p}
	for _, w := range ws {
		try("127.0.0.1:"+p, w)
		try(w, "127.0.0.1:"+p)
		for _, w2 := range ws {
			try(w, w2)
		}
	}
}
