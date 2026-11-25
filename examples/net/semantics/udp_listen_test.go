//go:build linux

package semantics

import (
	"errors"
	"net"
	"syscall"
	"testing"
)

// TestUDPListenForms (U1; Lean: udpAddrOf, ipv4Of, ValidDest, ListenStep).
// ListenUDP("udp4", &UDPAddr{IP, Port}) at a loopback address of the test
// range succeeds with the IP of 4 bytes, with the 16-byte IPv4-mapped form of
// the same IP (net.IPv4(...)), and with a junk Zone beside an IPv4 IP: the
// socket's LocalAddr is the same a.b.c.d:p in all three. Why (Go 1.27.3):
// ListenUDP -> sysListener.listenUDP -> internetSocket(SOCK_DGRAM) ->
// netFD.listenDatagram -> UDPAddr.sockaddr(AF_INET) -> ipToSockaddr ->
// ipToSockaddrInet4(ip, port) (net/ipsock_posix.go), which takes ip.To4()
// (4 bytes, or 16 with the ::ffff:0:0/96 prefix) and never looks at the Zone.
//
// Model: agrees. udpAddrOf turns both IP forms into the same canonical string
// (ipv4Of, as IP.To4) and ignores the Zone; ListenStep then allows the
// success. (notes/net-udp.md said the model panics unless the Zone is empty;
// Impl.lean's header says it is ignored for IPv4, which is what Go does.)
func TestUDPListenForms(t *testing.T) {
	t.Parallel()
	a := udpFreeAddr(t, "127.0.0.1")
	ip4 := net.IP{127, 0, 0, 1}
	for _, c := range []struct {
		name string
		addr *net.UDPAddr
	}{
		{"4-byte IP", &net.UDPAddr{IP: ip4, Port: a.Port}},
		{"16-byte IPv4-mapped IP", &net.UDPAddr{IP: net.IPv4(127, 0, 0, 1), Port: a.Port}},
		{"junk Zone", &net.UDPAddr{IP: ip4, Port: a.Port, Zone: "no-such-zone%42"}},
	} {
		if len(c.addr.IP) != 4 && len(c.addr.IP) != 16 {
			t.Fatalf("%s: IP of %d bytes", c.name, len(c.addr.IP))
		}
		forkMu.RLock() // the Close below must free the address at once (child_test.go)
		u, err := net.ListenUDP("udp4", c.addr)
		if err != nil {
			forkMu.RUnlock()
			t.Fatalf("%s: ListenUDP(%#v) = %v", c.name, c.addr, err)
		}
		got := laddr(u).String()
		u.Close()
		forkMu.RUnlock()
		if got != a.String() {
			t.Errorf("%s: LocalAddr %s, want %s", c.name, got, a)
		}
		t.Logf("%s (len(IP)=%d, Zone=%q): ListenUDP ok, LocalAddr %s", c.name, len(c.addr.IP), c.addr.Zone, got)
	}
	evidence(t, "U1", "4-byte, 16-byte mapped and junk-Zone IPv4 addresses all bind the same a.b.c.d:p", "allowed (udpAddrOf, ListenStep)")
}

// TestUDPListenTwice (U1; Lean: ListenStep, its sys failure). A second
// ListenUDP of the address of an open UDP socket of the same process fails
// with EADDRINUSE, shaped *net.OpError{Op "listen", Net "udp4", Source nil,
// Addr the *UDPAddr asked} > *os.SyscallError{Syscall "bind"} >
// syscall.EADDRINUSE (ListenUDP wraps listenUDP's error; listenDatagram
// returns os.NewSyscallError("bind", err): net/sock_posix.go). Go sets no
// SO_REUSEADDR and no SO_REUSEPORT on a unicast UDP socket (only on a
// multicast one, setDefaultMulticastSockopts; setDefaultSockopts sets only
// SO_BROADCAST for SOCK_DGRAM: net/sockopt_linux.go), measured by getsockopt:
// SO_REUSEADDR 0, SO_REUSEPORT 0, SO_BROADCAST 1. After the first socket's
// Close (the harness's; Close is not modeled, U12) the bind succeeds.
//
// Model: agrees, and over-approximates: ListenStep allows the failure (sys)
// and also a success (any node may bind any valid address, more than once).
func TestUDPListenTwice(t *testing.T) {
	t.Parallel()
	forkMu.RLock()
	defer forkMu.RUnlock()
	c := udpListen(t, "127.0.0.1")
	if v := udpSockopt(t, c, syscall.SOL_SOCKET, syscall.SO_REUSEADDR); v != 0 {
		t.Errorf("SO_REUSEADDR = %d, want 0", v)
	}
	if v := udpSockopt(t, c, syscall.SOL_SOCKET, soReusePort); v != 0 {
		t.Errorf("SO_REUSEPORT = %d, want 0", v)
	}
	bc := udpSockopt(t, c, syscall.SOL_SOCKET, syscall.SO_BROADCAST)
	t.Logf("sockopts: SO_REUSEADDR 0, SO_REUSEPORT 0, SO_BROADCAST %d", bc)
	a := laddr(c)
	_, err := net.ListenUDP("udp4", a)
	shape := udpShape(err)
	t.Logf("second ListenUDP(%v): %s", a, shape)
	var oe *net.OpError
	var se *syscallErr
	if !errors.As(err, &oe) || oe.Op != "listen" || oe.Net != "udp4" || oe.Source != nil || oe.Addr == nil {
		t.Fatalf("not *OpError{listen, udp4, Source nil, Addr set}: %s", shape)
	}
	if !errors.As(err, &se) || se.Syscall != "bind" || !errors.Is(err, syscall.EADDRINUSE) {
		t.Fatalf("not *os.SyscallError{bind} > EADDRINUSE: %s", shape)
	}
	c.Close()
	c2, err := net.ListenUDP("udp4", a)
	if err != nil {
		t.Fatalf("ListenUDP after Close: %v", err)
	}
	c2.Close()
	evidence(t, "U1", "second bind EADDRINUSE ("+shape+"); bind after Close ok", "allowed (ListenStep sys; success also allowed)")
}

// TestUDPListenNotLocal (U1; Lean: ListenStep's sys failure). A bind to an
// IPv4 address that is not this machine's (192.0.2.1, TEST-NET-1) fails with
// EADDRNOTAVAIL (Linux inet_bind: the address's type is not local and
// ip_nonlocal_bind is 0), shaped *net.OpError{listen, udp4, Source nil, Addr}
// > *os.SyscallError{bind} > EADDRNOTAVAIL.
//
// Model: agrees; it also allows the success (any node may bind any valid
// address: an over-approximation).
func TestUDPListenNotLocal(t *testing.T) {
	t.Parallel()
	a := &net.UDPAddr{IP: net.IP{192, 0, 2, 1}, Port: udpPortLo + 7}
	c, err := net.ListenUDP("udp4", a)
	if err == nil {
		c.Close()
		t.Fatalf("ListenUDP(%v) succeeded", a)
	}
	shape := udpShape(err)
	var se *syscallErr
	if !errors.As(err, &se) || se.Syscall != "bind" || !errors.Is(err, syscall.EADDRNOTAVAIL) {
		t.Fatalf("not bind EADDRNOTAVAIL: %s", shape)
	}
	evidence(t, "U1", "non-local bind: "+shape, "allowed (ListenStep sys)")
}

// TestUDPAndTCPSamePort (U1; Lean: udpExt separate from netExt). A TCP
// listener and a UDP socket bind the same ip:port, in either order, and both
// work: TCP and UDP have separate port tables in Linux (tcp_hashinfo,
// udp_table). Model: agrees (the two extensions share no state).
func TestUDPAndTCPSamePort(t *testing.T) {
	t.Parallel()
	u := udpListen(t, "127.0.0.1")
	a := laddr(u)
	ln, err := net.ListenTCP("tcp4", &net.TCPAddr{IP: a.IP, Port: a.Port})
	if err != nil {
		t.Fatalf("ListenTCP at the UDP socket's %v: %v", a, err)
	}
	defer ln.Close()
	// Both still work: a datagram to a, and a TCP connection to a.
	s := udpListen(t, "127.0.0.1")
	udpSend(t, s, []byte("udp"), a)
	if b, _, err := udpRecv(u, 16, guard); err != nil || string(b) != "udp" {
		t.Fatalf("UDP receive: %q, %v", b, err)
	}
	d, err := net.Dial("tcp4", a.String())
	if err != nil {
		t.Fatalf("TCP Dial %v: %v", a, err)
	}
	d.Close()
	evidence(t, "U1", "TCP listener and UDP socket at "+a.String()+" coexist", "allowed (separate extensions)")
}
