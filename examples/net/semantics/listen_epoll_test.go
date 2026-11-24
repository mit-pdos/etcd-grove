//go:build linux && amd64

package semantics

import (
	"errors"
	"fmt"
	"net"
	"os"
	"runtime"
	"strings"
	"syscall"
	"testing"
	"unsafe"
)

// TestListenEpollErrno (D6, D7, D8, D12; v3.6, Net/TrustedCode/net.lean's
// Listen.impl and model.epollErr). When the poller's registration of the new listening socket
// fails, net.Listen returns an *OpError{Op: "listen"} whose Err is the bare
// syscall.Errno of epoll_ctl(2), not an *os.SyscallError, and no listener (Go
// closes the socket). Go's path (go1.27.3): ListenConfig.Listen ->
// sysListener.listenMPTCP (MPTCP first, then plain TCP on any failure:
// mptcpsock_linux.go) -> listenTCPProto -> internetSocket -> socket
// (sock_posix.go), whose listenStream runs setsockopt(SO_REUSEADDR) (wrapped:
// os.NewSyscallError("setsockopt"), sockopt_linux.go), bind (wrapped "bind"),
// listen (wrapped "listen"), then `if err = fd.init(); err != nil { return err }`:
// unwrapped. fd.init is poll.FD.Init -> pollDesc.init
// (internal/poll/fd_poll_runtime.go), which returns errnoErr(syscall.Errno(errno))
// of runtime_pollOpen, the errno of epoll_ctl(EPOLL_CTL_ADD) (runtime/netpoll_epoll.go,
// netpollopen); errnoErr (errno_unix.go) keeps ENOMEM and ENOSPC as they are.
// socket then closes the fd, and Listen wraps the error in the *OpError
// (dial.go: `&OpError{Op: "listen", Net: sl.network, Source: nil, Addr: la, Err: err}`).
//
// Which errnos (documented, Linux fs/eventpoll.c, do_epoll_ctl and ep_insert):
// for a socket just made, ENOSPC (the user's watches reached
// fs.epoll.max_user_watches) or ENOMEM (an allocation of the epitem, its wait
// queue entry or the file's epitems head failed). The other errors are for a bad
// or closed fd (EBADF), one already registered (EEXIST), an epoll fd as target or
// a loop (EINVAL, ELOOP), or a file that cannot poll (EPERM): none applies. (EINTR
// only while the process is being killed.)
//
// Accept and Dial (D7, D8; v3.6, TCPListener.Accept.impl, Dial.impl,
// DialTimeout.impl and model.pollErr) register their new socket the same way and
// return the same unwrapped Errno: netFD.accept (fd_unix.go) does
// `if err = netfd.init(); err != nil { netfd.Close(); return nil, err }` after
// accept4(2) took a connection off the listener's queue (so the dialer then sees
// the connection closed: EOF on its read, measured here), and
// TCPListener.Accept wraps it as *OpError{Op: "accept"}; netFD.connect
// (fd_unix.go) does `if err := fd.pfd.Init(fd.net, true); err != nil { return
// nil, err }` after connect(2), socket (sock_posix.go) closes the fd, and
// dialSingle (dial.go) wraps it as *OpError{Op: "dial"}.
//
// Measured: the kernel's own ENOSPC needs lowering fs.epoll.max_user_watches
// (root, system-wide): not done. Instead the child (role "listen-epoll", with
// NETSEM_ADDR "op:errno") installs a seccomp filter (unprivileged, no_new_privs)
// that fails epoll_ctl(EPOLL_CTL_ADD) with the errno, after the poller is
// initialized (and, for accept, after a listener is open and a connection is
// queued on it by a raw connect(2) that bypasses the poller), then calls
// net.Listen, ln.Accept or net.Dial: Go's handling of the kernel's error is what
// is measured, the kernel's choice of errno is the documented part above.
// Before v3.6 the models always returned an *os.SyscallError for a sys failure
// (the outcome excluded: Listen.spec, Listener.Accept.spec and Dial.spec promised
// it).
func TestListenEpollErrno(t *testing.T) {
	t.Parallel()
	for _, op := range []string{"listen", "accept", "dial"} {
		for _, e := range []syscall.Errno{syscall.ENOSPC, syscall.ENOMEM} {
			ch := startChild(t, "listen-epoll", fmt.Sprintf("%s:%d", op, int(e)))
			got := ch.line(t)
			ch.kill(t)
			want := fmt.Sprintf("opError=true op=%s net=tcp addr=*net.TCPAddr errType=syscall.Errno errno=%d syscallError=false result=false newSockets=0", op, int(e))
			if op == "accept" {
				want += " peer=EOF"
			}
			if got != want {
				t.Errorf("%s with epoll_ctl failing %v:\n got %s\nwant %s", op, e, got, want)
			}
		}
	}
}

// The child's role is dispatched here (before TestMain, which knows the other
// roles: child_test.go), so that the amd64-only filter stays in this file.
func init() {
	if os.Getenv("NETSEM_CHILD") == "listen-epoll" {
		childListenEpoll(os.Getenv("NETSEM_ADDR"))
	}
}

// childListenEpoll is the child of TestListenEpollErrno: epoll_ctl(EPOLL_CTL_ADD)
// fails with errno from now on (all threads), then one net.Listen, Accept or
// Dial; it prints the error's shape, whether a result came back, how many
// sockets the call left open, and (accept) what the queued connection's dialer
// reads.
func childListenEpoll(arg string) {
	op, errno, ok := strings.Cut(arg, ":")
	var e int
	if _, err := fmt.Sscan(errno, &e); !ok || err != nil {
		childFail("arg %q: %v", arg, err)
	}
	// Initialize the poller (netpollinit's own epoll_ctl of its eventfd) before the filter.
	r, w, err := os.Pipe()
	if err != nil {
		childFail("pipe: %v", err)
	}
	defer r.Close()
	defer w.Close()
	var ln net.Listener
	raw := -1
	if op == "accept" || op == "dial" {
		if ln, err = net.Listen("tcp", "127.0.0.1:0"); err != nil {
			childFail("listen: %v", err)
		}
	}
	if op == "accept" { // a queued connection, its dialer outside the poller
		if raw, err = syscall.Socket(syscall.AF_INET, syscall.SOCK_STREAM, 0); err != nil {
			childFail("socket: %v", err)
		}
		port := ln.Addr().(*net.TCPAddr).Port
		if err := syscall.Connect(raw, &syscall.SockaddrInet4{Port: port, Addr: [4]byte{127, 0, 0, 1}}); err != nil {
			childFail("connect: %v", err)
		}
		tv := syscall.Timeval{Sec: 5}
		syscall.SetsockoptTimeval(raw, syscall.SOL_SOCKET, syscall.SO_RCVTIMEO, &tv)
	}
	before := countSockets()
	if err := failEpollCtlAdd(e); err != nil {
		childFail("seccomp: %v", err)
	}
	var res bool
	switch op {
	case "listen":
		var l net.Listener
		l, err = net.Listen("tcp", "127.0.0.1:0")
		res = l != nil
	case "accept":
		var c net.Conn
		c, err = ln.Accept()
		res = c != nil
	case "dial":
		var c net.Conn
		c, err = net.Dial("tcp", ln.Addr().String())
		res = c != nil
	default:
		childFail("op %q", op)
	}
	after := countSockets()
	var oe *net.OpError
	isOp := errors.As(err, &oe)
	eop, nw, addr, errType, errnoV := "", "", "", "", -1
	if isOp {
		eop, nw, addr = oe.Op, oe.Net, fmt.Sprintf("%T", oe.Addr)
		errType = fmt.Sprintf("%T", oe.Err)
		if en, ok := oe.Err.(syscall.Errno); ok {
			errnoV = int(en)
		}
	}
	var se *os.SyscallError
	out := fmt.Sprintf("opError=%v op=%s net=%s addr=%s errType=%s errno=%d syscallError=%v result=%v newSockets=%d",
		isOp, eop, nw, addr, errType, errnoV, errors.As(err, &se), res, after-before)
	if op == "accept" {
		buf := make([]byte, 1)
		n, rerr := syscall.Read(raw, buf)
		switch {
		case n == 0 && rerr == nil:
			out += " peer=EOF"
		default:
			out += fmt.Sprintf(" peer=%d,%v", n, rerr)
		}
	}
	fmt.Println(out)
	os.Exit(0)
}

// countSockets counts this process's fds that are sockets.
func countSockets() int {
	ents, err := os.ReadDir("/proc/self/fd")
	if err != nil {
		childFail("readdir: %v", err)
	}
	n := 0
	for _, e := range ents {
		if l, err := os.Readlink("/proc/self/fd/" + e.Name()); err == nil && strings.HasPrefix(l, "socket:") {
			n++
		}
	}
	return n
}

type sockFilter struct {
	code uint16
	jt   uint8
	jf   uint8
	k    uint32
}

type sockFprog struct {
	len    uint16
	_      [6]byte
	filter *sockFilter
}

// failEpollCtlAdd installs, on every thread of the process (SECCOMP_FILTER_FLAG_TSYNC),
// a seccomp filter failing epoll_ctl(_, EPOLL_CTL_ADD, ...) with errno and allowing
// every other system call.
func failEpollCtlAdd(errno int) error {
	const (
		ldAbs           = 0x20 // BPF_LD | BPF_W | BPF_ABS
		jeqK            = 0x15 // BPF_JMP | BPF_JEQ | BPF_K
		retK            = 0x06 // BPF_RET | BPF_K
		auditArchX86_64 = 0xc000003e
		retErrno        = 0x00050000 // SECCOMP_RET_ERRNO
		retAllow        = 0x7fff0000 // SECCOMP_RET_ALLOW
		sysSeccomp      = 317
		setModeFilter   = 1 // SECCOMP_SET_MODE_FILTER
		flagTsync       = 1 // SECCOMP_FILTER_FLAG_TSYNC
		prSetNoNewPrivs = 38
	)
	prog := []sockFilter{
		{ldAbs, 0, 0, 4}, // seccomp_data.arch
		{jeqK, 0, 5, auditArchX86_64},
		{ldAbs, 0, 0, 0}, // seccomp_data.nr
		{jeqK, 0, 3, uint32(syscall.SYS_EPOLL_CTL)},
		{ldAbs, 0, 0, 24}, // seccomp_data.args[1], low half
		{jeqK, 0, 1, syscall.EPOLL_CTL_ADD},
		{retK, 0, 0, retErrno | uint32(errno)},
		{retK, 0, 0, retAllow},
	}
	fp := sockFprog{len: uint16(len(prog)), filter: &prog[0]}
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()
	if _, _, e := syscall.RawSyscall6(syscall.SYS_PRCTL, prSetNoNewPrivs, 1, 0, 0, 0, 0); e != 0 {
		return fmt.Errorf("prctl(PR_SET_NO_NEW_PRIVS): %v", e)
	}
	if r, _, e := syscall.RawSyscall(sysSeccomp, setModeFilter, flagTsync, uintptr(unsafe.Pointer(&fp))); e != 0 || r != 0 {
		return fmt.Errorf("seccomp: %v (thread %d)", e, r)
	}
	runtime.KeepAlive(prog)
	return nil
}
