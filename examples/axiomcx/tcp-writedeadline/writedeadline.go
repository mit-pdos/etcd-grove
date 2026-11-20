// Package tcpwritedeadline is a counterexample to the net extension's D2/D5
// (GooseLang/Ext/Net/Impl.lean, WriteOutcome; notes/axiom-review/tcp-semantics.md,
// "v3"): a Write is one step of the semantics, which may return a timeout only
// if the end's write deadline is set at that step; but Go's Write is a loop of
// write(2) calls, and a deadline set by another goroutine while it blocks,
// after the peer has read some of its bytes, makes it return a timeout.
//
// Go's (*poll.FD).Write (internal/poll/fd_unix.go) checks the deadline once
// before the loop (prepareWrite) and then in every waitWrite: a Write blocked
// for buffer space returns (nn, poll.ErrDeadlineExceeded) as soon as another
// goroutine sets a deadline that has passed (SetDeadline wakes the poller,
// runtime_pollSetDeadline). In the semantics the Write's bytes must have been
// appended (its step taken) before the peer's Read returned one of them, and
// the deadline is set after that Read, so at the Write's step no deadline was
// set: WriteOutcome excludes the timeout.
//
// One node, at Addr: Main listens, dials itself and accepts; a second
// goroutine (reader) reads one byte at the acceptor's end and then sets the
// dialer's deadline to the present; Main writes 32 MiB at the dialer's end
// (more than loopback's socket buffers hold, so the Write blocks) and panics if
// the Write's error is a timeout (Timeout()) whose Err is not an
// *os.SyscallError (in Go: os.ErrDeadlineExceeded itself). Go: Main panics (in
// about 99 of 100 runs; in the others the new connection is reset, an
// *os.SyscallError). The semantics: the Write's error is never a timeout, its
// Err is an *os.SyscallError or net.ErrClosed, whose Timeout() is false, so
// Main never panics (Net/Proof/github_com/mit_pdos/etcd_grove/examples/
// axiomcx/tcp_writedeadline/Main.lean).
package tcpwritedeadline

import (
	"net"
	"os"
	"time"
)

// Addr is the node's listening address.
const Addr = "127.0.0.1:7197"

// Size is the Write's length: more than the socket buffers of a loopback
// connection hold (Linux 7.0's defaults: tcp_wmem's and tcp_rmem's maxima,
// 4 MiB and 6 MiB).
const Size = 1 << 25

// reader reads one byte at a and, if it got one, sets c's deadline to the
// present.
func reader(a, c net.Conn) {
	b := make([]byte, 1)
	if _, err := a.Read(b); err == nil {
		// one of the Write's bytes arrived: the Write has started
		c.SetDeadline(time.Now())
	}
}

// Main writes Size bytes to its own listener while another goroutine reads one
// of them at the other end and then sets the writer's deadline.
func Main() {
	l, err := net.Listen("tcp", Addr)
	if err != nil {
		return
	}
	c, err := net.Dial("tcp", Addr)
	if err != nil {
		return
	}
	a, err := l.Accept()
	if err != nil {
		return
	}
	go reader(a, c)
	_, err = c.Write(make([]byte, Size))
	if err != nil {
		oe := err.(*net.OpError)
		if _, ok := oe.Err.(*os.SyscallError); !ok && oe.Timeout() {
			panic("tcpwritedeadline: a Write timed out, its deadline set while it ran")
		}
	}
}
