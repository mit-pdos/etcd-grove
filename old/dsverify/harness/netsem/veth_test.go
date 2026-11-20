package netsem

import (
	"errors"
	"fmt"
	"io"
	"net"
	"os"
	"os/exec"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"testing"
	"time"
)

// The rig's topology (harness/rig/rig.py, Net.up, built by run-veth.sh with tag "netsem"):
// namespace dsrig-netsem-nI has eth0 = 10.77.0.(10+I)/24, a veth whose other end is on bridge
// br0 in dsrig-netsem-hub. Node 0 dials, node 1 listens, node 2 is a second dialer.
const vethTag = "dsrig-netsem-"

func nsName(i int) string { return sprintf("%sn%d", vethTag, i) }
func nsIP(i int) string   { return sprintf("10.77.0.%d", 10+i) }

// nsWorker runs functions on an OS thread that has joined a network namespace, so the sockets
// they create live there (a socket stays in the namespace it was made in, whichever thread uses
// it later). The thread is never unlocked: it exits with the worker, never returning to the pool.
type nsWorker chan func()

func newNSWorker(ns string) (nsWorker, error) {
	f, err := os.Open("/var/run/netns/" + ns)
	if err != nil {
		return nil, err
	}
	w := make(nsWorker)
	errc := make(chan error)
	go func() {
		runtime.LockOSThread()
		const sysSetns = 308 // linux/amd64
		_, _, e := syscall.RawSyscall(sysSetns, f.Fd(), syscall.CLONE_NEWNET, 0)
		f.Close()
		if e != 0 {
			errc <- fmt.Errorf("setns %s: %v", ns, e)
			return
		}
		errc <- nil
		for fn := range w {
			fn()
		}
	}()
	return w, <-errc
}

func (w nsWorker) do(f func()) {
	done := make(chan struct{})
	w <- func() { f(); close(done) }
	<-done
}

// inNS runs a command in namespace ns (ip netns exec).
func inNS(ns string, args ...string) error {
	out, err := exec.Command("ip", append([]string{"netns", "exec", ns}, args...)...).CombinedOutput()
	if err != nil {
		return fmt.Errorf("%s %v: %v %s", ns, args, err, out)
	}
	return nil
}

// netem sets (or with no args removes) a netem qdisc on node i's link, both directions, as the
// rig's delay fault does: on eth0 in the node's namespace and on its peer hI in the hub.
func netem(i int, args ...string) error {
	hub, h := vethTag+"hub", sprintf("h%d", i)
	if len(args) == 0 {
		inNS(nsName(i), "tc", "qdisc", "del", "dev", "eth0", "root")
		inNS(hub, "tc", "qdisc", "del", "dev", h, "root")
		return nil
	}
	if err := inNS(nsName(i), append([]string{"tc", "qdisc", "replace", "dev", "eth0", "root", "netem"}, args...)...); err != nil {
		return err
	}
	return inNS(hub, append([]string{"tc", "qdisc", "replace", "dev", h, "root", "netem"}, args...)...)
}

// partition drops every packet between nodes i and j (iptables DROP in INPUT and OUTPUT on
// both sides, as the rig's partition fault does); undo lifts it.
func partition(i, j int) (undo func(), err error) {
	var rules [][]string
	for _, p := range [][2]int{{i, j}, {j, i}} {
		rules = append(rules,
			[]string{nsName(p[0]), "OUTPUT", "-d", nsIP(p[1]), "-j", "DROP"},
			[]string{nsName(p[0]), "INPUT", "-s", nsIP(p[1]), "-j", "DROP"})
	}
	undo = func() {
		for _, r := range rules {
			inNS(r[0], append([]string{"iptables", "-w", "-D"}, r[1:]...)...)
		}
	}
	for _, r := range rules {
		if err := inNS(r[0], append([]string{"iptables", "-w", "-I"}, r[1:]...)...); err != nil {
			undo()
			return nil, err
		}
	}
	return undo, nil
}

// TestVeth runs the measured examples, and the measurements of AcceptAnyOrder and
// TimeoutOnBreak, with the two ends in two of the rig's namespaces over veth and the bridge.
// Skipped unless NETSEM_VETH=1 (run-veth.sh builds the namespaces and runs it as root).
func TestVeth(t *testing.T) {
	if os.Getenv("NETSEM_VETH") != "1" {
		t.Skip("needs the rig's namespaces (run-veth.sh)")
	}
	var w [3]nsWorker
	for i := range w {
		var err error
		if w[i], err = newNSWorker(nsName(i)); err != nil {
			t.Fatal(err)
		}
	}
	listenHost, inListenNS, inDialNS = nsIP(1), w[1].do, w[0].do
	t.Run("Examples", runExamples)
	t.Run("BreakInNetwork", func(t *testing.T) {
		out, err := breakInNetwork(func(args ...string) error {
			return inNS(nsName(1), append([]string{"iptables", "-w"}, args...)...)
		})
		if err != nil {
			t.Fatal(err)
		}
		t.Logf("BreakInNetwork: %s", out)
	})
	t.Run("AcceptOrder", func(t *testing.T) { acceptOrder(t, w) })
	t.Run("TimeoutOnBreak", func(t *testing.T) { timeoutOnBreak(t, w) })
}

// acceptOrder dials node 1's listener twice per trial, each dialer writing its id byte as soon
// as its Dial returns; node 1 accepts twice and reads the id from each. A trial is out of order
// when the first accepted connection is the one whose Dial returned second.
func acceptOrder(t *testing.T, w [3]nsWorker) {
	const trials = 1000
	extra := [3][]nsWorker{} // a second worker for nodes 0 and 2, for concurrent dials
	for i := range extra {
		x, err := newNSWorker(nsName(i))
		if err != nil {
			t.Fatal(err)
		}
		extra[i] = []nsWorker{w[i], x}
	}
	l, err := listen()
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	addr := l.Addr().String()

	// trial runs one trial: dials makes the two connections with dial, which records the order
	// in which the Dials returned (1, 2) and writes it as the connection's id byte.
	type dialFunc func(worker nsWorker) net.Conn
	trial := func(dials func(dial dialFunc) []net.Conn) (out bool, err error) {
		var ret atomic.Int32
		var mu sync.Mutex
		var dialErr error
		dial := func(worker nsWorker) net.Conn {
			var c net.Conn
			var e error
			worker.do(func() { c, e = net.Dial("tcp", addr) })
			if e != nil {
				mu.Lock()
				dialErr = e
				mu.Unlock()
				return nil
			}
			c.Write([]byte{byte(ret.Add(1))})
			return c
		}
		cs := dials(dial)
		defer func() {
			for _, c := range cs {
				if c != nil {
					c.Close()
				}
			}
		}()
		if dialErr != nil {
			return false, dialErr
		}
		l.(*net.TCPListener).SetDeadline(time.Now().Add(5 * time.Second))
		var first byte
		for k := 0; k < 2; k++ {
			a, err := l.Accept()
			if err != nil {
				return false, err
			}
			a.SetReadDeadline(time.Now().Add(5 * time.Second))
			b := make([]byte, 1)
			_, err = io.ReadFull(a, b)
			a.Close()
			if err != nil {
				return false, err
			}
			if k == 0 {
				first = b[0]
			}
		}
		return first == 2, nil
	}
	concurrent := func(wa, wb nsWorker) func(dialFunc) []net.Conn {
		return func(dial dialFunc) []net.Conn {
			cs := make([]net.Conn, 2)
			var wg sync.WaitGroup
			start := make(chan struct{})
			for k, wk := range []nsWorker{wa, wb} {
				wg.Add(1)
				go func() { defer wg.Done(); <-start; cs[k] = dial(wk) }()
			}
			close(start)
			wg.Wait()
			return cs
		}
	}
	backToBack := func(wa, wb nsWorker) func(dialFunc) []net.Conn {
		return func(dial dialFunc) []net.Conn {
			c1 := dial(wa)
			return []net.Conn{c1, dial(wb)}
		}
	}
	type mode struct {
		name  string
		setup func() error
		dials func(dialFunc) []net.Conn
	}
	modes := []mode{
		{"concurrent, both from node 0", nil, concurrent(extra[0][0], extra[0][1])},
		{"concurrent, from nodes 0 and 2", nil, concurrent(w[0], w[2])},
		{"back to back, both from node 0", nil, backToBack(extra[0][0], extra[0][1])},
		{"concurrent, nodes 0 and 2 with netem delay 2ms jitter 2ms",
			func() error {
				if err := netem(0, "delay", "2ms", "2ms"); err != nil {
					return err
				}
				return netem(2, "delay", "2ms", "2ms")
			}, concurrent(w[0], w[2])},
		{"back to back, node 0 (netem delay 5ms) then node 2 (none)",
			func() error {
				netem(2)
				return netem(0, "delay", "5ms")
			}, backToBack(w[0], w[2])},
	}
	defer netem(0)
	defer netem(2)
	for _, m := range modes {
		if m.setup != nil {
			if err := m.setup(); err != nil {
				t.Fatal(err)
			}
		}
		out, fails := 0, 0
		var firstErr error
		for k := 0; k < trials; k++ {
			o, err := trial(m.dials)
			if err != nil {
				fails++
				if firstErr == nil {
					firstErr = err
				}
				continue
			}
			if o {
				out++
			}
		}
		t.Logf("AcceptOrder %s: %d trials, %d accepted out of Dial-return order, %d failed (%v)",
			m.name, trials, out, fails, firstErr)
	}
}

// timeoutOnBreak breaks a connection from node 0 to node 1 by a partition and lets node 0's
// kernel give up on it, three ways: TCP_USER_TIMEOUT with unacknowledged data, keep-alive on an
// idle connection, and net.ipv4.tcp_retries2 (per namespace) with unacknowledged data. Node 0's
// blocked Read (no deadline) returns the kernel's error; then a few more Reads and Writes; then
// the partition is lifted and node 1 uses its end.
func timeoutOnBreak(t *testing.T, w [3]nsWorker) {
	const tcpUserTimeout = 18 // linux TCP_USER_TIMEOUT
	cases := []struct {
		name  string
		setup func(d *net.TCPConn) error
		data  bool
	}{
		{"TCP_USER_TIMEOUT 2s, unacknowledged data", func(d *net.TCPConn) error {
			rc, err := d.SyscallConn()
			if err != nil {
				return err
			}
			var serr error
			rc.Control(func(fd uintptr) {
				serr = syscall.SetsockoptInt(int(fd), syscall.IPPROTO_TCP, tcpUserTimeout, 2000)
			})
			return serr
		}, true},
		{"keep-alive idle 1s interval 1s count 2, idle", func(d *net.TCPConn) error {
			return d.SetKeepAliveConfig(net.KeepAliveConfig{Enable: true, Idle: time.Second, Interval: time.Second, Count: 2})
		}, false},
		{"tcp_retries2=3 in node 0, unacknowledged data", func(d *net.TCPConn) error {
			return inNS(nsName(0), "sysctl", "-qw", "net.ipv4.tcp_retries2=3")
		}, true},
	}
	defer inNS(nsName(0), "sysctl", "-qw", "net.ipv4.tcp_retries2=15")
	for _, c := range cases {
		d, a, err := pair()
		if err != nil {
			t.Fatal(err)
		}
		if err := c.setup(d.(*net.TCPConn)); err != nil {
			t.Fatal(err)
		}
		undo, err := partition(0, 1)
		if err != nil {
			t.Fatal(err)
		}
		start := time.Now()
		if c.data {
			if _, err := d.Write([]byte("unacknowledged")); err != nil {
				t.Fatal(err)
			}
		}
		done := make(chan error, 1)
		go func() { _, e := d.Read(make([]byte, 16)); done <- e }()
		var e error
		select {
		case e = <-done:
		case <-time.After(60 * time.Second):
			e = errors.New("no error within 60 s")
		}
		took := time.Since(start)
		var ne net.Error
		timeout, temporary := false, false
		if errors.As(e, &ne) {
			timeout, temporary = ne.Timeout(), ne.Temporary()
		}
		var later []string
		for k := 0; k < 2; k++ {
			d.SetReadDeadline(time.Now().Add(100 * time.Millisecond))
			_, e1 := d.Read(make([]byte, 16))
			later = append(later, "Read "+describe(e1))
		}
		for k := 0; k < 2; k++ {
			d.SetWriteDeadline(time.Now().Add(100 * time.Millisecond))
			_, e1 := d.Write([]byte("more"))
			later = append(later, "Write "+describe(e1))
		}
		undo()
		// Node 1's end, which never noticed: its Write draws a reset from node 0's kernel.
		_, ea1 := a.Write([]byte("reply"))
		time.Sleep(50 * time.Millisecond)
		got, aErrs := readAll(a, time.Second)
		t.Logf("TimeoutOnBreak %s: after %.1fs the blocked Read returned %q: errors.Is ETIMEDOUT %v, Timeout() %v, Temporary() %v, errors.Is os.ErrDeadlineExceeded %v; then %s; after the partition is lifted, node 1's Write %s, its Reads %d bytes then %v",
			c.name, took.Seconds(), errString(e), errors.Is(e, syscall.ETIMEDOUT), timeout, temporary,
			errors.Is(e, os.ErrDeadlineExceeded), strings.Join(later, ", "), describe(ea1), got, aErrs)
		d.Close()
		a.Close()
	}
}

func errString(e error) string {
	if e == nil {
		return "nil"
	}
	return e.Error()
}
