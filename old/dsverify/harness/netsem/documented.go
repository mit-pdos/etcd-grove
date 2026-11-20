package netsem

import (
	"errors"
	"net"
)

// The decisions below are not measured by the examples TestExamples runs; each says where its
// evidence comes from (AcceptAnyOrder and TimeoutOnBreak are measured by veth_test.go, which
// run-veth.sh runs). The functions are illustrations: no test calls them.

// AcceptAnyOrder: Accept returns any connection dialed to the listener and not yet accepted,
// not the oldest: a Dial returns when the dialer's handshake step is done, and the listener's
// kernel queues the connection when the last ACK arrives, so two concurrent dials can be queued
// in either order.
//
// Lean: Impl.lean, Listener.pending ("in no particular order"), NetConnStep "Accept"
// (`cid ∈ l.pending`, `List.erase`).
// Evidence: documented (the TCP handshake; Linux's accept queue is filled by the final ACK);
// measured (veth_test.go, acceptOrder, over the rig's veth links, 1000 trials each): node 0's
// link with netem delay 5 ms, node 0 dials, and when its Dial has returned node 2 dials: node 2's
// connection is accepted first in 1000 of 1000 trials (node 0's final ACK is still on the wire).
// Two concurrent dials (each Dial's return numbered by an atomic counter right after it, so near
// ties are approximate): 87 of 1000 out of order from one node, 71 from two nodes, 157 from two
// nodes with netem delay 2 ms jitter 2 ms. Back to back from one node without delay: 0 of 1000.
// Allowed: c2 accepted before c1 although Dial(c1) returned first.
func AcceptAnyOrder(l net.Listener, addr string) {
	c1, _ := net.Dial("tcp", addr)
	c2, _ := net.Dial("tcp", addr)
	first, _ := l.Accept() // c1's or c2's acceptor end
	_, _, _ = c1, c2, first
}

// ReadShape: a Read returns either n > 0 bytes and a nil error, or no bytes and an error (or
// (0, nil) for an empty buffer); never bytes together with an error.
//
// Lean: Impl.lean, ReadOutcome (every case with an error has `data = []`).
// Evidence: documented (Go 1.27 src/internal/poll/fd_unix.go, FD.Read: one read(2); on an error
// n is set to 0; eofError turns (0, nil) into io.EOF; src/net/net.go, conn.Read).
func ReadShape(c net.Conn) {
	buf := make([]byte, 8)
	n, err := c.Read(buf)
	// allowed: n > 0 && err == nil; n == 0 && err != nil
	// excluded: n > 0 && err != nil
	_, _ = n, err
}

// TimeoutOnBreak: a break may report Timeout() == true: when the kernel gives up retransmitting
// or keep-alive probing, the error is ETIMEDOUT, whose Timeout() is true, and the connection is
// dead, not usable as after a deadline. A program that retries on every timeout can loop on a
// broken connection (safe, but it must not assume the stream is intact).
//
// Lean: TrustedCode/net.lean, model.codeErr (a break's Timeout()/Temporary() are arbitrary).
// Evidence: documented (src/syscall/syscall_unix.go, Errno.Timeout: EAGAIN, EWOULDBLOCK,
// ETIMEDOUT; src/net/net.go, OpError.Timeout unwraps os.SyscallError); measured (veth_test.go,
// timeoutOnBreak: a connection from node 0 to node 1, a partition by iptables DROP in both
// namespaces, node 0's Read blocked with no deadline): with TCP_USER_TIMEOUT 2 s and
// unacknowledged data the Read returns "read: connection timed out" after 2.3 s; with keep-alive
// (idle 1 s, interval 1 s, count 2) on an idle connection after 3.1 s; with net.ipv4.tcp_retries2=3
// in node 0's namespace and unacknowledged data after 3.2 s. Each time errors.Is(err,
// syscall.ETIMEDOUT), Timeout() and Temporary() are true and errors.Is(err, os.ErrDeadlineExceeded)
// is false; the next two Reads return io.EOF and the next two Writes EPIPE (the break as the
// model has it: an error, then EOF). After the partition is lifted, node 1's end, which noticed
// nothing, writes successfully, then reads 0 of the 14 bytes node 0 wrote (the lost suffix),
// ECONNRESET, EOF, EOF.
func TimeoutOnBreak(c net.Conn) {
	_, err := c.Read(make([]byte, 8))
	var ne net.Error
	if errors.As(err, &ne) && ne.Timeout() {
		// allowed: the connection was broken (ETIMEDOUT), not only a deadline
	}
}

// AddressSpelling: the model matches Dial's address string with Listen's literally (after
// resolving a wildcard host to the node's own IP, NodeIdentity in node_identity_netns_test.go).
// The claimed configuration spells every address as "IP:port", the same at the listener and its
// dialers, with distinct IPs for distinct nodes (one network namespace and one IP per node).
// Outside it the model is wrong: e.g. Dial("10.0.0.1:8000") to a node that listened on
// "010.0.0.1:8000" succeeds in Go and is stuck in the model.
//
// Lean: Impl.lean, NetConnStep "Listen" (`l.addr ≠ a`, `a = listenAddr me addr`), "Dial"
// (`l.addr = addr`).
// Evidence: assumed (a property of the deployment; the kits generate the addresses).
func AddressSpelling() {
	_, _ = net.Listen("tcp", "10.0.0.1:8000")
	_, _ = net.Dial("tcp", "10.0.0.1:8000")
}

// InOrderOnce: within a connection, bytes are delivered in the order written, each at most once,
// unmodified; across connections nothing is ordered.
//
// Lean: Impl.lean, Stream.bytes (a queue: Write appends, Read removes a prefix), Conn.Breaks
// (only a suffix is lost).
// Evidence: assumed of Linux TCP (sequence numbers, checksums; a corrupted segment that passes
// the 16-bit checksum is outside the model, as for every TCP user).
func InOrderOnce() {}
