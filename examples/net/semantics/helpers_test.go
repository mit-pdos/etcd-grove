//go:build linux

package semantics

import (
	"errors"
	"io"
	"net"
	"os"
	"strings"
	"syscall"
	"testing"
	"time"
	"unsafe"
)

// Kernel probes. They look at a socket without changing it: TCP_INFO's state
// does not consume a pending error (getsockopt(SO_ERROR) would), and SIOCINQ
// counts the received, unread bytes without reading them. The tests use them
// to wait (bounded) until a segment has arrived, so that no assertion depends
// on a sleep.

const (
	tcpEstablished = 1
	tcpClose       = 7      // after a RST (or both sides closed)
	tcpCloseWait   = 8      // after a FIN from the peer
	siocInq        = 0x541B // SIOCINQ = FIONREAD
	waitLimit      = 5 * time.Second
	guard          = 5 * time.Second // a read that should not block is bounded by this
)

func rawFd(t *testing.T, c syscall.Conn, f func(fd uintptr)) {
	t.Helper()
	rc, err := c.SyscallConn()
	if err != nil {
		t.Fatalf("SyscallConn: %v", err)
	}
	if err := rc.Control(f); err != nil {
		t.Fatalf("Control: %v", err)
	}
}

// tcpState is the socket's TCP state (tcpi_state, the first byte of tcp_info).
func tcpState(t *testing.T, c syscall.Conn) int {
	var st int
	var serr error
	rawFd(t, c, func(fd uintptr) {
		st, serr = syscall.GetsockoptInt(int(fd), syscall.IPPROTO_TCP, syscall.TCP_INFO)
	})
	if serr != nil {
		t.Fatalf("getsockopt TCP_INFO: %v", serr)
	}
	return st & 0xff
}

// inq is the number of received bytes not yet read.
func inq(t *testing.T, c syscall.Conn) int {
	var n int32
	var errno syscall.Errno
	rawFd(t, c, func(fd uintptr) {
		_, _, errno = syscall.Syscall(syscall.SYS_IOCTL, fd, siocInq, uintptr(unsafe.Pointer(&n)))
	})
	if errno != 0 {
		t.Fatalf("ioctl SIOCINQ: %v", errno)
	}
	return int(n)
}

func waitFor(t *testing.T, what string, cond func() bool) {
	t.Helper()
	end := time.Now().Add(waitLimit)
	for !cond() {
		if time.Now().After(end) {
			t.Fatalf("timed out (%v) waiting for %s", waitLimit, what)
		}
		time.Sleep(time.Millisecond)
	}
}

func waitState(t *testing.T, c syscall.Conn, st int) {
	t.Helper()
	waitFor(t, "TCP state "+stateName(st), func() bool { return tcpState(t, c) == st })
}

func waitInq(t *testing.T, c syscall.Conn, n int) {
	t.Helper()
	waitFor(t, "unread bytes to arrive", func() bool { return inq(t, c) >= n })
}

func stateName(st int) string {
	switch st {
	case tcpEstablished:
		return "ESTABLISHED"
	case tcpClose:
		return "CLOSE"
	case tcpCloseWait:
		return "CLOSE_WAIT"
	}
	return "state?"
}

// pair is a fresh loopback connection: d is the dialer's end, a the
// acceptor's. Both are closed at the end of the test.
func pair(t *testing.T) (d, a *net.TCPConn) {
	t.Helper()
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("Listen: %v", err)
	}
	defer ln.Close()
	type res struct {
		c   net.Conn
		err error
	}
	ch := make(chan res, 1)
	go func() {
		c, err := ln.Accept()
		ch <- res{c, err}
	}()
	dc, err := net.Dial("tcp", ln.Addr().String())
	if err != nil {
		t.Fatalf("Dial: %v", err)
	}
	r := <-ch
	if r.err != nil {
		t.Fatalf("Accept: %v", r.err)
	}
	t.Cleanup(func() { dc.Close(); r.c.Close() })
	return dc.(*net.TCPConn), r.c.(*net.TCPConn)
}

// name classifies an error the way the decisions speak of it.
func name(err error) string {
	switch {
	case err == nil:
		return "nil"
	case err == io.EOF:
		return "EOF"
	case errors.Is(err, net.ErrClosed):
		return "ErrClosed"
	case errors.Is(err, os.ErrDeadlineExceeded):
		return "timeout"
	case errors.Is(err, syscall.ECONNRESET):
		return "ECONNRESET"
	case errors.Is(err, syscall.EPIPE):
		return "EPIPE"
	case errors.Is(err, syscall.ENOTCONN):
		return "ENOTCONN"
	case errors.Is(err, syscall.ECONNREFUSED):
		return "ECONNREFUSED"
	case errors.Is(err, syscall.EADDRINUSE):
		return "EADDRINUSE"
	}
	return "other(" + err.Error() + ")"
}

// readSeq reads (buffers of 64 bytes, each read bounded by guard) until the
// first EOF or after max results, and returns what each Read returned:
// "data:<bytes>" or the error's name.
func readSeq(t *testing.T, c net.Conn, max int) string {
	t.Helper()
	var out []string
	for i := 0; i < max; i++ {
		c.SetReadDeadline(time.Now().Add(guard))
		buf := make([]byte, 64)
		n, err := c.Read(buf)
		if n > 0 {
			out = append(out, "data:"+string(buf[:n]))
		}
		if err != nil {
			out = append(out, name(err))
			if err == io.EOF {
				break
			}
		}
	}
	c.SetReadDeadline(time.Time{})
	return strings.Join(out, " ")
}

// mustWrite writes and fails the test on an error.
func mustWrite(t *testing.T, c net.Conn, s string) {
	t.Helper()
	if n, err := c.Write([]byte(s)); err != nil || n != len(s) {
		t.Fatalf("Write(%q) = %d, %v", s, n, err)
	}
}

// resetBy makes peer send a RST on the connection: peer gets one unread
// byte from c, then closes (Linux: close with unread input sends RST, RFC
// 2525 section 2.17). It waits until c's socket has received the RST.
func resetBy(t *testing.T, c, peer *net.TCPConn) {
	t.Helper()
	mustWrite(t, c, "u")
	waitInq(t, peer, 1)
	if err := peer.Close(); err != nil {
		t.Fatalf("peer Close: %v", err)
	}
	waitState(t, c, tcpClose)
}
