package tcpemptywrite

import (
	"errors"
	"net"
	"os"
	"syscall"
	"testing"
	"time"
)

// panics runs f and returns what it panicked with (nil if it returned).
func panics(f func()) (r any) {
	defer func() { r = recover() }()
	f()
	return nil
}

// TestMainPanics: Main panics (the expired deadline makes the empty Write
// fail, deterministically). One run per process: a panicking run leaves its
// sockets open (repeat with go test -count=1 in a loop).
func TestMainPanics(t *testing.T) {
	if r := panics(Main); r == nil {
		t.Fatal("Main returned without panicking")
	} else {
		t.Logf("Main panicked: %v", r)
	}
}

// resetAddr is mainReset's address.
const resetAddr = "127.0.0.1:7198"

// mainReset is Main's variant without a deadline (not translated; the same
// semantic step excludes its run): it dials its own listener and accepts the
// connection; the dialer writes a byte, the acceptor closes without reading
// it (Linux sends a RST), the dialer's Read returns once the RST arrives
// (ECONNRESET), and the dialer writes no bytes: Go returns EPIPE.
func mainReset() {
	l, err := net.Listen("tcp", resetAddr)
	if err != nil {
		return
	}
	c, err := net.Dial("tcp", resetAddr)
	if err != nil {
		l.Close()
		return
	}
	s, err := l.Accept()
	if err != nil {
		c.Close()
		l.Close()
		return
	}
	one := make([]byte, 1)
	if _, err := c.Write(one); err != nil {
		c.Close()
		s.Close()
		l.Close()
		return
	}
	time.Sleep(50 * time.Millisecond) // let the byte arrive, so that the Close resets
	s.Close()
	c.Read(one)
	if _, err := c.Write(make([]byte, 0)); err != nil {
		panic("tcpemptywrite: a Write of no bytes failed after a reset")
	}
	c.Close()
	l.Close()
}

// TestMainResetPanics: mainReset panics (the reset makes the empty Write fail).
func TestMainResetPanics(t *testing.T) {
	if r := panics(mainReset); r == nil {
		t.Fatal("mainReset returned without panicking")
	} else {
		t.Logf("mainReset panicked: %v", r)
	}
}

// TestEmptyWriteErrors: the errors themselves. An empty Write: on a fresh
// connection, (0, nil); with an expired write deadline, (0, timeout); after
// a RST, (0, ECONNRESET) if nothing took the error yet, else (0, EPIPE);
// after CloseWrite, (0, EPIPE).
func TestEmptyWriteErrors(t *testing.T) {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	pair := func() (*net.TCPConn, *net.TCPConn) {
		ch := make(chan net.Conn, 1)
		go func() { c, _ := ln.Accept(); ch <- c }()
		d, err := net.Dial("tcp", ln.Addr().String())
		if err != nil {
			t.Fatal(err)
		}
		return d.(*net.TCPConn), (<-ch).(*net.TCPConn)
	}
	report := func(what string, n int, err error) {
		t.Logf("%-44s n=%d err=%v (timeout=%v EPIPE=%v ECONNRESET=%v)", what, n, err,
			errors.Is(err, os.ErrDeadlineExceeded), errors.Is(err, syscall.EPIPE),
			errors.Is(err, syscall.ECONNRESET))
	}
	{
		d, a := pair()
		n, err := d.Write(nil)
		report("fresh", n, err)
		if err != nil {
			t.Errorf("fresh: %v", err)
		}
		d.SetWriteDeadline(time.Now())
		n, err = d.Write(nil)
		report("expired write deadline", n, err)
		if n != 0 || !errors.Is(err, os.ErrDeadlineExceeded) {
			t.Errorf("expired deadline: want 0, timeout")
		}
		d.SetWriteDeadline(time.Time{})
		n, err = d.Write(nil)
		report("deadline cleared", n, err)
		d.CloseWrite()
		n, err = d.Write(nil)
		report("after CloseWrite", n, err)
		d.Close()
		a.Close()
	}
	for _, take := range []bool{false, true} {
		d, a := pair()
		d.Write([]byte("u"))
		time.Sleep(50 * time.Millisecond)
		a.Close() // unread byte: RST
		time.Sleep(50 * time.Millisecond)
		if take {
			n, err := d.Read(make([]byte, 1))
			report("Read after RST", n, err)
		}
		what := "empty Write after RST, no Read"
		if take {
			what = "empty Write after RST and the Read"
		}
		n, err := d.Write(nil)
		report(what, n, err)
		if err == nil {
			t.Errorf("%s: succeeded", what)
		}
		n, err = d.Write(nil)
		report("  and again", n, err)
		d.Close()
	}
}
