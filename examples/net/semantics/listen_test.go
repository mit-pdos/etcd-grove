//go:build linux

package semantics

import (
	"errors"
	"net"
	"testing"
	"time"
)

// TestListenTwice (D6: "only failure if this node has an open listener at a
// (EADDRINUSE)"). A second Listen at the address of an open listener fails
// with EADDRINUSE. Once that listener is closed, Listen at the address
// succeeds, even while a connection accepted at it is still open (Go sets
// SO_REUSEADDR; bind refuses only a port with a listening socket). Supports
// D6. (Under forkMu: a concurrent fork would keep the closed listener open,
// child_test.go, and the last Listen would fail, which D6 allows.)
func TestListenTwice(t *testing.T) {
	t.Parallel()
	forkMu.RLock()
	defer forkMu.RUnlock()
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	addr := ln.Addr().String()
	if l2, err := net.Listen("tcp", addr); name(err) != "EADDRINUSE" {
		if l2 != nil {
			l2.Close()
		}
		t.Fatalf("second Listen at %s: %v; want EADDRINUSE", addr, err)
	}
	c, err := net.Dial("tcp", addr)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	s, err := ln.Accept()
	if err != nil {
		t.Fatal(err)
	}
	defer s.Close()
	if err := ln.Close(); err != nil {
		t.Fatal(err)
	}
	l3, err := net.Listen("tcp", addr)
	if err != nil {
		t.Fatalf("Listen at %s after its listener's Close, a connection open: %v; want success", addr, err)
	}
	l3.Close()
}

// TestListenTakenByOtherProcess (D6). A listener of another process at the
// address also makes Listen fail with EADDRINUSE. In the model, another node
// (on the same host) holding the address does not force the failure:
// failure is always allowed, success there is more than Linux (sound).
// Supports D6 (as an over-approximation).
func TestListenTakenByOtherProcess(t *testing.T) {
	t.Parallel()
	ch := startChild(t, "listen", "")
	addr := ch.line(t)
	if l, err := net.Listen("tcp", addr); name(err) != "EADDRINUSE" {
		if l != nil {
			l.Close()
		}
		t.Fatalf("Listen at the child's %s: %v; want EADDRINUSE", addr, err)
	}
}

// freeAddr is an address with no listener: the kernel picks a port for a
// listener that is then closed.
func freeAddr(t *testing.T) string {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	addr := ln.Addr().String()
	ln.Close()
	return addr
}

// TestDialRefused (D8: "or failure (refused, ...)"). Dial of an address with
// no listener fails with ECONNREFUSED (the kernel answers the SYN with RST).
// Retried on a fresh port if another test took this one in between.
// Supports D8. (Under forkMu: a concurrent fork keeps freeAddr's closed
// listener open for a moment, child_test.go; measured, the Dial then
// completed and failed with ECONNRESET.)
func TestDialRefused(t *testing.T) {
	t.Parallel()
	forkMu.RLock()
	defer forkMu.RUnlock()
	for i := 0; ; i++ {
		c, err := net.Dial("tcp", freeAddr(t))
		if err == nil {
			c.Close()
			if i < 5 {
				continue
			}
			t.Fatal("Dial of a closed port kept succeeding")
		}
		if name(err) != "ECONNREFUSED" {
			t.Fatalf("Dial with no listener: %v; want ECONNREFUSED", err)
		}
		return
	}
}

// TestAcceptAfterListenerClose (D7: "l closed: error only"; D9: "closed if
// open (nil); error if already closed"). Close of a listener returns nil and
// wakes a blocked Accept with ErrClosed; every later Accept returns
// ErrClosed, and a second Close returns ErrClosed. Supports D7, D9.
func TestAcceptAfterListenerClose(t *testing.T) {
	t.Parallel()
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	done := make(chan error, 1)
	go func() {
		_, err := ln.Accept()
		done <- err
	}()
	time.Sleep(10 * time.Millisecond) // lets Accept block; the outcome is the same if it has not
	if err := ln.Close(); err != nil {
		t.Fatalf("listener Close: %v", err)
	}
	select {
	case err := <-done:
		if !errors.Is(err, net.ErrClosed) {
			t.Fatalf("blocked Accept after Close: %v; want ErrClosed", err)
		}
	case <-time.After(waitLimit):
		t.Fatal("Accept still blocked after Close")
	}
	if _, err := ln.Accept(); !errors.Is(err, net.ErrClosed) {
		t.Fatalf("Accept after Close: %v; want ErrClosed", err)
	}
	if err := ln.Close(); !errors.Is(err, net.ErrClosed) {
		t.Fatalf("second listener Close: %v; want ErrClosed", err)
	}
}

// TestPendingAtListenerClose (D7, D8, D9: "Pending connections stay
// pending"). Dial succeeds with no Accept (the kernel completes the
// handshake into the listener's queue), and the dialer's Write succeeds.
// When the listener is closed, the kernel resets the queued connections:
// the dialer reads ECONNRESET, then EOF. A new listener at the same address
// does not get the old connection (its Accept times out). So Linux never
// lets a connection pending at a closed listener be accepted later; the
// model allows it (D7, more than Linux), and allows the dialer's cut (D1).
// Supports D7-D9 as an over-approximation.
func TestPendingAtListenerClose(t *testing.T) {
	t.Parallel()
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	addr := ln.Addr().String()
	c, err := net.Dial("tcp", addr)
	if err != nil {
		t.Fatalf("Dial with no Accept: %v; want success", err)
	}
	defer c.Close()
	mustWrite(t, c, "lost")
	ln.Close()
	waitState(t, c.(*net.TCPConn), tcpClose)
	if got := readSeq(t, c, 3); got != "ECONNRESET EOF" {
		t.Fatalf("dialer's reads after the listener's Close = %q; want ECONNRESET EOF", got)
	}
	l2, err := net.Listen("tcp", addr)
	if err != nil {
		t.Fatal(err)
	}
	defer l2.Close()
	l2.(*net.TCPListener).SetDeadline(time.Now().Add(100 * time.Millisecond))
	if s, err := l2.Accept(); name(err) != "timeout" {
		if s != nil {
			s.Close()
		}
		t.Fatalf("Accept on a new listener at the address: %v; want timeout (nothing pending)", err)
	}
}
