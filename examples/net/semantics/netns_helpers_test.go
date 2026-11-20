//go:build linux && amd64

package semantics

import (
	"bufio"
	"bytes"
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

// The network-namespace tests (netns_test.go): their topology, and how they
// get root without making the plain `go test` privileged.
//
// Gate. A namespace test is skipped unless NET_NETNS=1. Unprivileged user
// namespaces are blocked on the measuring machine (apparmor), so the test
// re-executes its own binary as root, `sudo -n env NET_NETNS=1 <binary>
// -test.run '^TestX$'`, and passes or fails with it, logging its output;
// run as root (euid 0), it runs the body itself. Nothing else in the package
// runs as root.
//
// Topology. Three namespaces, created fresh for each test and named
// net-<pid>-<n>-{c,r,s}: the client c (10.213.1.1, eth0), the router r
// (10.213.1.254 on c0, 10.213.2.254 on s0, forwarding) and the server s
// (10.213.2.1, eth0), joined by two veth pairs created inside the namespaces
// (`ip -n c link add eth0 type veth peer name c0 netns r`), so no link, address,
// route, sysctl or iptables rule is ever made in the host's namespace. The
// faults are iptables rules in the router's FORWARD chain only, so neither
// end's kernel sees a local error (a DROP in an end's own OUTPUT chain makes
// its transmissions fail locally with EPERM, which is not a network fault):
// to both ends, a partition is packets lost in the network, and a REJECT
// --reject-with tcp-reset is a middlebox's reset.
//
// Sockets. A socket lives in the namespace of the thread that created it, so
// the server's Listen and the client's Dial run on an OS thread that joined
// the namespace (nsWorker, setns(2)); the sockets they return are then used
// from any goroutine. Accept's sockets are in the listener's namespace.
//
// Cleanup. Each test registers, with t.Cleanup, the removal of every rule it
// inserts and of its namespaces (which also removes their links and rules),
// so a failing test leaves nothing; the unprivileged parent also deletes the
// namespaces by name after the root child exits, in case the child was
// killed before its own cleanups ran.

const (
	nsCliIP   = "10.213.1.1"
	nsRtrCli  = "10.213.1.254"
	nsSrvIP   = "10.213.2.1"
	nsRtrSrv  = "10.213.2.254"
	sysSetns  = 308 // linux/amd64 setns(2); the syscall package has no SYS_SETNS
	tcpUserTO = 18  // TCP_USER_TIMEOUT, linux/tcp.h
)

var netnsSeq atomic.Int32

// netnsTest gates and runs a namespace test: the body runs as root, with a
// fresh topology.
func netnsTest(t *testing.T, body func(t *testing.T, n *netnsTopo)) {
	if os.Getenv("NET_NETNS") != "1" {
		t.Skip("a network-namespace test: set NET_NETNS=1 (needs sudo -n)")
	}
	tag := os.Getenv("NET_NETNS_TAG")
	if tag == "" {
		tag = fmt.Sprintf("net-%d-%d", os.Getpid(), netnsSeq.Add(1))
	}
	if os.Geteuid() != 0 {
		t.Parallel()
		netnsAsRoot(t, tag)
		return
	}
	body(t, newNetnsTopo(t, tag))
}

// netnsAsRoot re-runs the current test in the test binary as root.
func netnsAsRoot(t *testing.T, tag string) {
	cmd := exec.Command("sudo", "-n", "env", "NET_NETNS=1", "NET_NETNS_TAG="+tag,
		os.Args[0], "-test.run=^"+t.Name()+"$", "-test.v", "-test.count=1", "-test.timeout=100s")
	var out bytes.Buffer
	cmd.Stdout, cmd.Stderr = &out, &out
	t.Cleanup(func() {
		// The child's own cleanups removed them, unless it was killed.
		for _, r := range []string{"c", "r", "s"} {
			ns := tag + "-" + r
			if _, err := os.Stat("/run/netns/" + ns); err == nil {
				forkMu.Lock()
				exec.Command("sudo", "-n", "ip", "netns", "del", ns).Run()
				forkMu.Unlock()
			}
		}
	})
	forkMu.Lock() // as startChild: keep this fork out of the tests that need Close at once
	err := cmd.Start()
	forkMu.Unlock()
	if err != nil {
		t.Fatalf("sudo: %v", err)
	}
	err = cmd.Wait()
	sc := bufio.NewScanner(&out)
	for sc.Scan() {
		if l := strings.TrimSpace(sc.Text()); l != "" && !strings.HasPrefix(l, "=== RUN") {
			t.Log(l)
		}
	}
	if err != nil {
		t.Fatalf("the test as root (sudo -n): %v", err)
	}
}

type netnsTopo struct {
	cliNS, rtrNS, srvNS string
	cli, srv            nsWorker
}

func nsCmd(args ...string) error {
	out, err := exec.Command(args[0], args[1:]...).CombinedOutput()
	if err != nil {
		return fmt.Errorf("%s: %v %s", strings.Join(args, " "), err, bytes.TrimSpace(out))
	}
	return nil
}

func mustNsCmd(t *testing.T, args ...string) {
	t.Helper()
	if err := nsCmd(args...); err != nil {
		t.Fatal(err)
	}
}

func newNetnsTopo(t *testing.T, tag string) *netnsTopo {
	n := &netnsTopo{cliNS: tag + "-c", rtrNS: tag + "-r", srvNS: tag + "-s"}
	for _, ns := range []string{n.cliNS, n.rtrNS, n.srvNS} {
		mustNsCmd(t, "ip", "netns", "add", ns)
		t.Cleanup(func() { nsCmd("ip", "netns", "del", ns) })
		mustNsCmd(t, "ip", "-n", ns, "link", "set", "lo", "up")
	}
	for _, c := range [][]string{
		{"-n", n.cliNS, "link", "add", "eth0", "type", "veth", "peer", "name", "c0", "netns", n.rtrNS},
		{"-n", n.srvNS, "link", "add", "eth0", "type", "veth", "peer", "name", "s0", "netns", n.rtrNS},
		{"-n", n.cliNS, "addr", "add", nsCliIP + "/24", "dev", "eth0"},
		{"-n", n.srvNS, "addr", "add", nsSrvIP + "/24", "dev", "eth0"},
		{"-n", n.rtrNS, "addr", "add", nsRtrCli + "/24", "dev", "c0"},
		{"-n", n.rtrNS, "addr", "add", nsRtrSrv + "/24", "dev", "s0"},
		{"-n", n.cliNS, "link", "set", "eth0", "up"},
		{"-n", n.srvNS, "link", "set", "eth0", "up"},
		{"-n", n.rtrNS, "link", "set", "c0", "up"},
		{"-n", n.rtrNS, "link", "set", "s0", "up"},
		{"-n", n.cliNS, "route", "add", "default", "via", nsRtrCli},
		{"-n", n.srvNS, "route", "add", "default", "via", nsRtrSrv},
	} {
		mustNsCmd(t, append([]string{"ip"}, c...)...)
	}
	mustNsCmd(t, "ip", "netns", "exec", n.rtrNS, "sysctl", "-qw", "net.ipv4.ip_forward=1")
	var err error
	if n.cli, err = newNSWorker(t, n.cliNS); err != nil {
		t.Fatal(err)
	}
	if n.srv, err = newNSWorker(t, n.srvNS); err != nil {
		t.Fatal(err)
	}
	return n
}

// nsWorker runs functions on an OS thread that joined a network namespace
// (dsverify-lab's harness/netsem/veth_test.go). The thread stays locked, so
// it exits with the worker's goroutine instead of returning to the pool.
type nsWorker chan func()

func newNSWorker(t *testing.T, ns string) (nsWorker, error) {
	f, err := os.Open("/run/netns/" + ns)
	if err != nil {
		return nil, err
	}
	w := make(nsWorker)
	errc := make(chan error)
	go func() {
		runtime.LockOSThread()
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
	if err := <-errc; err != nil {
		return nil, err
	}
	t.Cleanup(func() { close(w) })
	return w, nil
}

func (w nsWorker) do(f func()) {
	done := make(chan struct{})
	w <- func() { f(); close(done) }
	<-done
}

// listen makes a listener at the server's address, port chosen by its kernel.
func (n *netnsTopo) listen(t *testing.T) *net.TCPListener {
	t.Helper()
	var l net.Listener
	var err error
	n.srv.do(func() { l, err = net.Listen("tcp", nsSrvIP+":0") })
	if err != nil {
		t.Fatalf("Listen in %s: %v", n.srvNS, err)
	}
	t.Cleanup(func() { l.Close() })
	return l.(*net.TCPListener)
}

// dial dials addr from the client's namespace on worker w (nil: the client's).
func (n *netnsTopo) dial(w nsWorker, addr string) (*net.TCPConn, error) {
	if w == nil {
		w = n.cli
	}
	var c net.Conn
	var err error
	w.do(func() { c, err = net.Dial("tcp", addr) })
	if err != nil {
		return nil, err
	}
	return c.(*net.TCPConn), nil
}

// pair is a connection from the client to the server across the router: d the
// dialer's end (client), a the acceptor's (server); both closed at the end.
// The first Dial retries (bounded) while the links come up.
func (n *netnsTopo) pair(t *testing.T) (d, a *net.TCPConn) {
	t.Helper()
	l := n.listen(t)
	ch := make(chan net.Conn, 1)
	go func() {
		c, err := l.Accept()
		if err != nil {
			c = nil
		}
		ch <- c
	}()
	end := time.Now().Add(waitLimit)
	for {
		var err error
		if d, err = n.dial(nil, l.Addr().String()); err == nil {
			break
		}
		if time.Now().After(end) {
			t.Fatalf("Dial %s from %s: %v", l.Addr(), n.cliNS, err)
		}
		time.Sleep(10 * time.Millisecond)
	}
	var ac net.Conn
	select {
	case ac = <-ch:
	case <-time.After(waitLimit):
	}
	if ac == nil {
		t.Fatal("Accept failed")
	}
	l.Close()
	t.Cleanup(func() { d.Close(); ac.Close() })
	return d, ac.(*net.TCPConn)
}

// rule inserts an iptables rule in the router's chain; the returned undo (also
// a cleanup) deletes it, once.
func (n *netnsTopo) rule(t *testing.T, spec ...string) (undo func()) {
	t.Helper()
	ipt := func(op string) error {
		return nsCmd(append([]string{"ip", "netns", "exec", n.rtrNS, "iptables", "-w", op}, spec...)...)
	}
	if err := ipt("-I"); err != nil {
		t.Fatal(err)
	}
	var once sync.Once
	undo = func() {
		once.Do(func() {
			if err := ipt("-D"); err != nil {
				t.Errorf("removing the rule: %v", err)
			}
		})
	}
	t.Cleanup(undo)
	return undo
}

// partition drops, in the router, every packet between the client and the
// server, both ways; heal lifts it.
func (n *netnsTopo) partition(t *testing.T) (heal func()) {
	t.Helper()
	u1 := n.rule(t, "FORWARD", "-s", nsCliIP, "-d", nsSrvIP, "-j", "DROP")
	u2 := n.rule(t, "FORWARD", "-s", nsSrvIP, "-d", nsCliIP, "-j", "DROP")
	return func() { u1(); u2() }
}

func setUserTimeout(t *testing.T, c *net.TCPConn, ms int) {
	t.Helper()
	var serr error
	rawFd(t, c, func(fd uintptr) {
		serr = syscall.SetsockoptInt(int(fd), syscall.IPPROTO_TCP, tcpUserTO, ms)
	})
	if serr != nil {
		t.Fatalf("TCP_USER_TIMEOUT: %v", serr)
	}
}

// Errors as E1 speaks of them.

func errnoName(e syscall.Errno) string {
	switch e {
	case syscall.ETIMEDOUT:
		return "ETIMEDOUT"
	case syscall.ECONNRESET:
		return "ECONNRESET"
	case syscall.EPIPE:
		return "EPIPE"
	case syscall.ENOTCONN:
		return "ENOTCONN"
	case syscall.EHOSTUNREACH:
		return "EHOSTUNREACH"
	case syscall.EPERM:
		return "EPERM"
	}
	return fmt.Sprintf("Errno(%d)", int(e))
}

// short names an error: nil, EOF, timeout (a deadline's), ErrClosed, or the
// errno of an *os.SyscallError in an *net.OpError ("sys:ETIMEDOUT"); anything
// else in full.
func short(err error) string {
	if err == nil {
		return "nil"
	}
	if err == io.EOF {
		return "EOF"
	}
	if errors.Is(err, os.ErrDeadlineExceeded) {
		return "timeout"
	}
	if errors.Is(err, net.ErrClosed) {
		return "ErrClosed"
	}
	if e, ok := sysErrno(err); ok {
		return "sys:" + errnoName(e)
	}
	return fmt.Sprintf("other(%T %v)", err, err)
}

// sysErrno: err is an *net.OpError whose Err is an *os.SyscallError wrapping a
// syscall.Errno (E1's kind sys, as Go's netFD builds it: wrapSyscallError).
func sysErrno(err error) (syscall.Errno, bool) {
	oe, ok := err.(*net.OpError)
	if !ok {
		return 0, false
	}
	se, ok := oe.Err.(*os.SyscallError)
	if !ok {
		return 0, false
	}
	e, ok := se.Err.(syscall.Errno)
	return e, ok && e != 0
}

// chain is err's full shape: every link of its Unwrap chain with its type,
// then Timeout(), Temporary() and errors.Is(err, os.ErrDeadlineExceeded).
func chain(err error) string {
	if err == nil {
		return "nil"
	}
	if err == io.EOF {
		return "io.EOF"
	}
	var parts []string
	for e := err; e != nil; e = errors.Unwrap(e) {
		switch x := e.(type) {
		case *net.OpError:
			parts = append(parts, fmt.Sprintf("*net.OpError{Op:%q Net:%q}", x.Op, x.Net))
		case *os.SyscallError:
			parts = append(parts, fmt.Sprintf("*os.SyscallError{Syscall:%q}", x.Syscall))
		case syscall.Errno:
			parts = append(parts, "syscall."+errnoName(x))
		default:
			parts = append(parts, fmt.Sprintf("%T", e))
		}
	}
	var ne net.Error
	timeout, temporary := false, false
	if errors.As(err, &ne) {
		timeout, temporary = ne.Timeout(), ne.Temporary()
	}
	return fmt.Sprintf("%s, Timeout()=%v Temporary()=%v Is(os.ErrDeadlineExceeded)=%v",
		strings.Join(parts, " > "), timeout, temporary, errors.Is(err, os.ErrDeadlineExceeded))
}

// reads reads (64-byte buffers) up to max times, each bounded by per (a
// timeout ends the sequence, as EOF does), and returns what each returned:
// "data:<bytes>" or short(err).
func reads(c net.Conn, per time.Duration, max int) string {
	var out []string
	for i := 0; i < max; i++ {
		c.SetReadDeadline(time.Now().Add(per))
		buf := make([]byte, 64)
		k, err := c.Read(buf)
		if k > 0 {
			out = append(out, "data:"+string(buf[:k]))
		}
		if err != nil {
			out = append(out, short(err))
			if err == io.EOF || errors.Is(err, os.ErrDeadlineExceeded) {
				break
			}
		}
	}
	c.SetReadDeadline(time.Time{})
	return strings.Join(out, " ")
}

// writeRes is a Write's (n, short(err)).
func writeRes(c net.Conn, s string) string {
	k, err := c.Write([]byte(s))
	return fmt.Sprintf("(%d, %s)", k, short(err))
}

// evidence logs a test's verdict line in one format: the decisions, the
// outcome, whether the model allows it.
func evidence(t *testing.T, decisions, outcome, model string) {
	t.Helper()
	t.Logf("EVIDENCE %s | observed: %s | model: %s", decisions, outcome, model)
}
