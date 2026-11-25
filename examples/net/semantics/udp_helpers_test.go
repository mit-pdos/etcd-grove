//go:build linux

package semantics

import (
	"bufio"
	"errors"
	"fmt"
	"math/rand/v2"
	"net"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"syscall"
	"testing"
	"time"
)

// Helpers of the UDP tests (udp_*_test.go): the UDP extension's evidence
// (GooseLang/Ext/Udp/Impl.lean, decisions U1-U13).
//
// Ports. The model's valid addresses (Net.addrOk, D20) have a port outside
// the ephemeral range (32768-60999, ip_local_port_range's default), so the
// tests bind explicit ports, drawn at random from udpPortLo..udpPortHi and
// redrawn while the bind fails with EADDRINUSE (the tests run in parallel).

const (
	udpPortLo = 20000
	udpPortHi = 30000
	udpShort  = 300 * time.Millisecond // a read that should time out (nothing comes) waits this long
)

// udpListen binds a fresh "udp4" socket at ip and a free port of the test
// range; it is closed at the end of the test.
func udpListen(t *testing.T, ip string) *net.UDPConn {
	t.Helper()
	for i := 0; i < 200; i++ {
		a := &net.UDPAddr{IP: net.ParseIP(ip).To4(), Port: udpPortLo + rand.IntN(udpPortHi-udpPortLo)}
		c, err := net.ListenUDP("udp4", a)
		if err == nil {
			t.Cleanup(func() { c.Close() })
			return c
		}
		if !errors.Is(err, syscall.EADDRINUSE) {
			t.Fatalf("ListenUDP(%v): %v", a, err)
		}
	}
	t.Fatalf("no free UDP port in %d..%d", udpPortLo, udpPortHi)
	return nil
}

// udpFreeAddr is an address at ip whose port no socket is bound to (bound,
// then closed: a port the test range's draws then avoid only by chance, a
// collision with a parallel test being improbable).
func udpFreeAddr(t *testing.T, ip string) *net.UDPAddr {
	t.Helper()
	forkMu.RLock() // a fork would keep the closed socket bound for a moment (child_test.go)
	defer forkMu.RUnlock()
	c := udpListen(t, ip)
	a := c.LocalAddr().(*net.UDPAddr)
	c.Close()
	return a
}

func laddr(c *net.UDPConn) *net.UDPAddr { return c.LocalAddr().(*net.UDPAddr) }

// udpInq is SIOCINQ of a UDP socket: the payload length of the first queued
// datagram (Linux udp_ioctl, first_packet_length), 0 when none is queued. It
// reads nothing.
func udpInq(t *testing.T, c *net.UDPConn) int { return inq(t, c) }

// udpWaitQueued waits (bounded) until a datagram with a non-empty payload is
// queued at c.
func udpWaitQueued(t *testing.T, c *net.UDPConn) {
	t.Helper()
	waitFor(t, "a datagram to be queued", func() bool { return udpInq(t, c) > 0 })
}

// udpSend sends b to a and fails the test unless WriteToUDP returns (len(b), nil).
func udpSend(t *testing.T, c *net.UDPConn, b []byte, a *net.UDPAddr) {
	t.Helper()
	n, err := c.WriteToUDP(b, a)
	if err != nil || n != len(b) {
		t.Fatalf("WriteToUDP(%d bytes, %v) = %d, %v", len(b), a, n, err)
	}
}

// udpRecv is a ReadFromUDP of a buffer of size n, bounded by d (the harness's
// deadline; the model has none).
func udpRecv(c *net.UDPConn, n int, d time.Duration) ([]byte, *net.UDPAddr, error) {
	c.SetReadDeadline(time.Now().Add(d))
	defer c.SetReadDeadline(time.Time{})
	buf := make([]byte, n)
	k, from, err := c.ReadFromUDP(buf)
	if k < 0 || k > n {
		panic(fmt.Sprintf("ReadFromUDP returned n = %d for a buffer of %d", k, n))
	}
	return buf[:k], from, err
}

// udpShape is an error's full shape: each link of its chain, with an
// *net.OpError's Op, Net, Source and Addr (nil or the address), an
// *os.SyscallError's Syscall, an Errno's number and name.
func udpShape(err error) string {
	if err == nil {
		return "nil"
	}
	var parts []string
	for e := err; e != nil; e = errors.Unwrap(e) {
		switch x := e.(type) {
		case *net.OpError:
			src, addr := "nil", "nil"
			if x.Source != nil {
				src = fmt.Sprintf("%T(%v)", x.Source, x.Source)
			}
			if x.Addr != nil {
				addr = fmt.Sprintf("%T(%v)", x.Addr, x.Addr)
			}
			parts = append(parts, fmt.Sprintf("*net.OpError{Op:%q Net:%q Source:%s Addr:%s}", x.Op, x.Net, src, addr))
		case *os.SyscallError:
			parts = append(parts, fmt.Sprintf("*os.SyscallError{Syscall:%q}", x.Syscall))
		case syscall.Errno:
			parts = append(parts, fmt.Sprintf("syscall.Errno(%d %q)", int(x), x.Error()))
		default:
			if e == net.ErrClosed {
				parts = append(parts, "net.ErrClosed")
			} else {
				parts = append(parts, fmt.Sprintf("%T(%v)", e, e))
			}
		}
	}
	return strings.Join(parts, " > ")
}

// udpSockopt is getsockopt(level, opt) of c's socket, as an int.
func udpSockopt(t *testing.T, c syscall.Conn, level, opt int) int {
	t.Helper()
	var v int
	var serr error
	rawFd(t, c, func(fd uintptr) { v, serr = syscall.GetsockoptInt(int(fd), level, opt) })
	if serr != nil {
		t.Fatalf("getsockopt(%d, %d): %v", level, opt, serr)
	}
	return v
}

// procUDPQueue is the rx_queue (bytes queued for reading) of the socket bound
// to a in /proc/net/udp of the reading process's network namespace, and
// whether there is one. It reads another process's socket without touching it.
func procUDPQueue(t *testing.T, a *net.UDPAddr) (int, bool) {
	t.Helper()
	f, err := os.Open("/proc/net/udp")
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	ip := a.IP.To4()
	// /proc/net/udp prints the address as the host-order u32 of the
	// network-order bytes: little-endian on amd64.
	want := fmt.Sprintf("%02X%02X%02X%02X:%04X", ip[3], ip[2], ip[1], ip[0], a.Port)
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		fs := strings.Fields(sc.Text())
		if len(fs) > 4 && fs[1] == want {
			q := strings.SplitN(fs[4], ":", 2) // tx_queue:rx_queue, hex
			rx, _ := strconv.ParseInt(q[1], 16, 64)
			return int(rx), true
		}
	}
	return 0, false
}

// A child process for the UDP tests: the test binary re-run on the helper
// test TestUDPHelperProcess (UDPSEM_CHILD set to the role, UDPSEM_ADDR the
// address), reporting on stdout, killed by the parent (child_test.go's child,
// its line and kill).

func startUDPChild(t *testing.T, role, addr string) *child {
	t.Helper()
	cmd := exec.Command(os.Args[0], "-test.run=^TestUDPHelperProcess$")
	cmd.Env = append(os.Environ(), "UDPSEM_CHILD="+role, "UDPSEM_ADDR="+addr)
	cmd.Stderr = os.Stderr
	out, err := cmd.StdoutPipe()
	if err != nil {
		t.Fatal(err)
	}
	forkMu.Lock()
	err = cmd.Start()
	forkMu.Unlock()
	if err != nil {
		t.Fatal(err)
	}
	ch := &child{cmd, bufio.NewReader(out)}
	t.Cleanup(func() { cmd.Process.Kill(); cmd.Wait() })
	return ch
}

// TestUDPHelperProcess is not a test: it is the body of a child process of
// the UDP tests (startUDPChild), and skips otherwise.
func TestUDPHelperProcess(t *testing.T) {
	role := os.Getenv("UDPSEM_CHILD")
	if role == "" {
		t.Skip("the body of a child process (startUDPChild)")
	}
	switch role {
	case "bind": // bind UDPSEM_ADDR, say "ready", never read
		a, err := net.ResolveUDPAddr("udp4", os.Getenv("UDPSEM_ADDR"))
		if err != nil {
			childFail("resolve: %v", err)
		}
		c, err := net.ListenUDP("udp4", a)
		if err != nil {
			childFail("listen: %v", err)
		}
		fmt.Println("ready")
		_ = c
		select {}
	default:
		childFail("unknown role %q", role)
	}
}

// udpCounters is a namespace's /proc/net/snmp as "Ip.FragCreates" -> value,
// read in the network namespace ns by ip netns exec ("" the current one).
func udpCounters(t *testing.T, ns string) map[string]int64 {
	t.Helper()
	var out []byte
	var err error
	if ns == "" {
		out, err = os.ReadFile("/proc/net/snmp")
	} else {
		out, err = exec.Command("ip", "netns", "exec", ns, "cat", "/proc/net/snmp").Output()
	}
	if err != nil {
		t.Fatalf("reading /proc/net/snmp in %q: %v", ns, err)
	}
	m := map[string]int64{}
	lines := strings.Split(strings.TrimSpace(string(out)), "\n")
	for i := 0; i+1 < len(lines); i += 2 {
		hs, vs := strings.Fields(lines[i]), strings.Fields(lines[i+1])
		if len(hs) != len(vs) || len(hs) == 0 {
			continue
		}
		proto := strings.TrimSuffix(hs[0], ":")
		for j := 1; j < len(hs); j++ {
			v, _ := strconv.ParseInt(vs[j], 10, 64)
			m[proto+"."+hs[j]] = v
		}
	}
	return m
}

// counterDelta is after-before for the named counters, "name=+d ...".
func counterDelta(before, after map[string]int64, names ...string) map[string]int64 {
	d := map[string]int64{}
	for _, n := range names {
		d[n] = after[n] - before[n]
	}
	return d
}

// syscallErr is os.SyscallError, for errors.As.
type syscallErr = os.SyscallError

// soReusePort is SO_REUSEPORT (asm-generic/socket.h; the syscall package has no name for it).
const soReusePort = 15
