// Package tcpemptywrite is a counterexample to the TCP extension's D2
// (GooseLang/Ext/Tcp/Impl.lean, WriteOutcome; notes/axiom-review/tcp-semantics.md):
// a Write of no bytes on an end that is not closed and has not shut its write
// side can fail on Linux, while WriteOutcome lets it only succeed (its
// failures all write fewer bytes than asked, k < len(bs), impossible for
// len(bs) = 0).
//
// Go's (*poll.FD).Write (internal/poll/fd_unix.go) checks the write deadline
// (prepareWrite) before any write(2), and calls write(2) even for an empty
// buffer, returning its error with nn = 0 = len(p): an expired write deadline
// gives (0, timeout); a reset connection gives (0, ECONNRESET or EPIPE),
// since tcp_sendmsg_locked checks the socket's error and state before it
// looks at the length (the test's mainReset).
//
// One node, at Addr: Main dials its own listener, sets a deadline that has
// passed (time.Now()), and writes nothing. Go: the Write returns a timeout and
// Main panics, every run. The semantics: the Write succeeds, so Main never
// panics (NetTcp/Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/
// tcp_emptywrite/Main.lean).
package tcpemptywrite

import (
	"net"
	"time"
)

// Addr is the node's listening address.
const Addr = "127.0.0.1:7199"

// Main dials its own listener, sets a deadline that has passed, and writes
// no bytes.
func Main() {
	l, err := net.Listen("tcp", Addr)
	if err != nil {
		return
	}
	c, err := net.Dial("tcp", Addr)
	if err != nil {
		l.Close()
		return
	}
	c.SetDeadline(time.Now())
	if _, err := c.Write(make([]byte, 0)); err != nil {
		panic("tcpemptywrite: a Write of no bytes failed")
	}
	c.Close()
	l.Close()
}
