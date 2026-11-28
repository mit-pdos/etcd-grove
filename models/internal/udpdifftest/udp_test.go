// Package udpdifftest runs the same tests against Go's net and against net with its Go model spliced
// in (models/net/model.go, the UDP part: etcd-grove#58), whose stubs' Go bodies are plain blocking
// sockets (etc/gomodels.py, row net-udp). They exercise what the model replaces under Go's own
// ListenUDP, WriteToUDP and ReadFromUDP (sysListener.listenUDP, UDPConn.writeTo, UDPConn.readFrom),
// and Go's code above it (ok(), the *OpErrors, the network's switch), on loopback, in the shapes the
// specs state (Net/Spec/net/{ListenUDP,UDPConn__WriteToUDP,UDPConn__ReadFromUDP}.lean): what the
// model leaves arbitrary (addresses, error names and numbers, D18, U9, U10) is checked only for its
// shape. No test closes a socket: Close on a *UDPConn is not modelled (U12, the model is stuck; in
// gc builds it blocks forever), and the sockets go when the test process exits (U7). Not tested here
// (the model is stuck or the extension panics, so no verified program reaches them): the networks
// "udp" and "udp6", wildcard and non-IPv4 addresses, a nil address to WriteToUDP, connected sockets.
package udpdifftest

import (
	"bytes"
	"errors"
	"math/rand"
	"net"
	"os"
	"syscall"
	"testing"
)

// listen binds a UDP socket at 127.0.0.1 on a free port below Linux's ephemeral range (as the UDP
// extension's valid addresses, U1).
func listen(t *testing.T) (*net.UDPConn, *net.UDPAddr) {
	t.Helper()
	for i := 0; i < 1000; i++ {
		a := &net.UDPAddr{IP: []byte{127, 0, 0, 1}, Port: 20000 + rand.Intn(12000)}
		c, err := net.ListenUDP("udp4", a)
		if err == nil {
			return c, a
		}
	}
	t.Fatal("no free UDP port")
	return nil, nil
}

// checkOpError: err is an *OpError of op on "udp4" with the given Source and Addr, whose Err is a
// system call's error (an *os.SyscallError around a nonzero Errno, or, for listen, a bare one).
func checkOpError(t *testing.T, err error, op string, src, addr net.Addr, bareOk bool) {
	t.Helper()
	var oe *net.OpError
	if !errors.As(err, &oe) || oe.Op != op || oe.Net != "udp4" || oe.Source != src || oe.Addr != addr {
		t.Fatalf("error %#v: want an *OpError{Op: %q, Net: \"udp4\", Source: %v, Addr: %v}", err, op, src, addr)
	}
	switch e := oe.Err.(type) {
	case *os.SyscallError:
		if n, ok := e.Err.(syscall.Errno); !ok || n == 0 {
			t.Fatalf("Err %#v: want a nonzero Errno inside", e)
		}
	case syscall.Errno:
		if !bareOk || e == 0 {
			t.Fatalf("Err %#v: a bare Errno", e)
		}
	default:
		t.Fatalf("Err %#v: want a system call's error", oe.Err)
	}
}

// TestUDPSendRecv: datagrams of at most 524 bytes (U3) arrive whole; WriteToUDP returns (len(b),
// nil), ReadFromUDP (len(d), a non-nil *UDPAddr, nil); a socket's LocalAddr is a non-nil *UDPAddr
// and its RemoteAddr nil (conn's methods, Go's).
func TestUDPSendRecv(t *testing.T) {
	c1, _ := listen(t)
	c2, a2 := listen(t)
	if la, ok := c1.LocalAddr().(*net.UDPAddr); !ok || la == nil {
		t.Fatalf("LocalAddr %#v: want a non-nil *UDPAddr", c1.LocalAddr())
	}
	if ra := c1.RemoteAddr(); ra != nil {
		t.Fatalf("RemoteAddr %#v: want nil", ra)
	}
	buf := make([]byte, 2048)
	for _, size := range []int{0, 1, 100, 524} {
		b := make([]byte, size)
		rand.Read(b)
		n, err := c1.WriteToUDP(b, a2)
		if n != size || err != nil {
			t.Fatalf("WriteToUDP of %d bytes: (%d, %v)", size, n, err)
		}
		n, from, err := c2.ReadFromUDP(buf)
		if n != size || from == nil || err != nil || !bytes.Equal(buf[:n], b) {
			t.Fatalf("ReadFromUDP of %d bytes: (%d, %v, %v)", size, n, from, err)
		}
	}
}

// TestUDPShortBuffer (U4): a read into a buffer shorter than the datagram returns its first len(b)
// bytes, the bytes of the underlying array past them unchanged, and the rest of the datagram is gone
// (the next read is the next datagram).
func TestUDPShortBuffer(t *testing.T) {
	c1, _ := listen(t)
	c2, a2 := listen(t)
	d1 := bytes.Repeat([]byte{'x'}, 100)
	d2 := []byte("next")
	for _, d := range [][]byte{d1, d2} {
		if _, err := c1.WriteToUDP(d, a2); err != nil {
			t.Fatal(err)
		}
	}
	buf := bytes.Repeat([]byte{'.'}, 10)
	n, _, err := c2.ReadFromUDP(buf[:6])
	if n != 6 || err != nil || string(buf) != "xxxxxx...." {
		t.Fatalf("short read: (%d, %v), buffer %q", n, err, buf)
	}
	n, _, err = c2.ReadFromUDP(buf)
	if n != 4 || err != nil || string(buf[:n]) != "next" {
		t.Fatalf("next read: (%d, %v), buffer %q", n, err, buf)
	}
}

// TestUDPZeroConn: a zero UDPConn's WriteToUDP and ReadFromUDP fail with syscall.EINVAL (Go's
// c.ok()).
func TestUDPZeroConn(t *testing.T) {
	var c net.UDPConn
	if n, err := c.WriteToUDP([]byte("x"), &net.UDPAddr{IP: []byte{127, 0, 0, 1}, Port: 20000}); n != 0 || err != syscall.EINVAL {
		t.Fatalf("WriteToUDP: (%d, %v)", n, err)
	}
	if n, a, err := c.ReadFromUDP(make([]byte, 1)); n != 0 || a != nil || err != syscall.EINVAL {
		t.Fatalf("ReadFromUDP: (%d, %v, %v)", n, a, err)
	}
}

// TestUDPUnknownNetwork: ListenUDP of a network that is not UDP is Go's *OpError with an
// UnknownNetworkError.
func TestUDPUnknownNetwork(t *testing.T) {
	a := &net.UDPAddr{IP: []byte{127, 0, 0, 1}, Port: 20000}
	c, err := net.ListenUDP("tcp", a)
	var oe *net.OpError
	if c != nil || !errors.As(err, &oe) || oe.Op != "listen" || oe.Net != "tcp" || oe.Source != nil ||
		oe.Addr != net.Addr(a) || oe.Err != net.UnknownNetworkError("tcp") {
		t.Fatalf("ListenUDP(\"tcp\"): (%v, %#v)", c, err)
	}
}

// TestUDPListenInUse (U1, U9): a second bind of a bound address fails (Linux: EADDRINUSE; the model
// allows the failure), with Go's *OpError{Op: "listen", Source: nil, Addr: laddr} and a nil
// *UDPConn.
func TestUDPListenInUse(t *testing.T) {
	_, a := listen(t)
	c, err := net.ListenUDP("udp4", a)
	if c != nil {
		t.Fatalf("second ListenUDP: %v", c)
	}
	checkOpError(t, err, "listen", nil, a, true)
	t.Logf("second bind: %v", err)
}
