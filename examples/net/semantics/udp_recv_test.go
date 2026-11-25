//go:build linux

package semantics

import (
	"bytes"
	"errors"
	"fmt"
	"net"
	"os"
	"syscall"
	"testing"
)

// TestUDPRecvTruncates (U4; Lean: RecvStep, d.take n). ReadFromUDP with a
// buffer of 10 bytes, a 100-byte datagram queued and a second one behind it:
// n = 10, err = nil, the datagram's first 10 bytes and the sender's address;
// the rest of the datagram is discarded, and the next ReadFromUDP returns the
// second datagram. Why: recvfrom(2) without MSG_TRUNC copies min(len, size)
// and drops the datagram (udp_recvmsg sets MSG_TRUNC in msg_flags and
// returns the copied length; Go reads no flags: poll.FD.ReadFromInet4 returns
// recvfrom's n, internal/poll/fd_unix.go). The second datagram is sent only
// once the first is queued (SIOCINQ), so that their order is fixed.
//
// Model: agrees (RecvStep returns d.take n, success; the datagram is not
// consumed in the model, which also allows it again: over-approximation).
func TestUDPRecvTruncates(t *testing.T) {
	t.Parallel()
	s, r := udpListen(t, "127.0.0.1"), udpListen(t, "127.0.0.1")
	d1 := make([]byte, 100)
	for i := range d1 {
		d1[i] = byte('a' + i%26)
	}
	udpSend(t, s, d1, laddr(r))
	udpWaitQueued(t, r)
	udpSend(t, s, []byte("second"), laddr(r))
	got, from, err := udpRecv(r, 10, guard)
	if err != nil || !bytes.Equal(got, d1[:10]) || from == nil || from.String() != laddr(s).String() {
		t.Fatalf("truncated read: %q, %v, %s", got, from, udpShape(err))
	}
	got2, _, err := udpRecv(r, 200, guard)
	if err != nil || string(got2) != "second" {
		t.Fatalf("next read: %q, %v (want the second datagram: the first's rest discarded)", got2, err)
	}
	evidence(t, "U4", fmt.Sprintf("100-byte datagram, 10-byte buffer: (10, %q, sender, nil); next read: %q", got, got2),
		"allowed (RecvStep: d.take n)")
}

// TestUDPRecvEmptyBuffer (U4; Lean: RecvStep with n = 0). ReadFromUDP with a
// zero-length buffer: Go has no shortcut for len(p) == 0 (poll.FD.ReadFromInet4
// calls recvfrom(2) whatever len(p) is; contrast poll.FD.Read's "if len(p) ==
// 0 { return 0, nil }": internal/poll/fd_unix.go). Measured: with nothing
// queued it blocks (here until the harness's deadline: timeout); with a
// 5-byte datagram queued it returns n = 0, err = nil and the sender's address,
// and the datagram is consumed (SIOCINQ then 0, and the next read times out).
//
// Model: agrees (RecvStep: d.take 0 = [], success; the model's stutter is the
// blocking; it does not consume, which allows more).
func TestUDPRecvEmptyBuffer(t *testing.T) {
	t.Parallel()
	s, r := udpListen(t, "127.0.0.1"), udpListen(t, "127.0.0.1")
	if _, _, err := udpRecv(r, 0, udpShort); !errors.Is(err, os.ErrDeadlineExceeded) {
		t.Fatalf("empty read with nothing queued: %s, want a block (timeout)", udpShape(err))
	}
	udpSend(t, s, []byte("hello"), laddr(r))
	udpWaitQueued(t, r)
	got, from, err := udpRecv(r, 0, guard)
	if len(got) != 0 || err != nil || from == nil || from.String() != laddr(s).String() {
		t.Fatalf("empty read with a datagram queued: %d, %v, %s", len(got), from, udpShape(err))
	}
	q := udpInq(t, r)
	_, _, err2 := udpRecv(r, 64, udpShort)
	if q != 0 || !errors.Is(err2, os.ErrDeadlineExceeded) {
		t.Fatalf("after the empty read: SIOCINQ %d, next read %s (want consumed)", q, udpShape(err2))
	}
	evidence(t, "U4", "empty buffer: blocks with nothing queued; (0, sender, nil) with a datagram, which is consumed",
		"allowed (RecvStep n = 0)")
}

// TestUDPZeroValue (U9, U13; Lean: none: the trusted models check the id 0
// before calling the extension). A zero-value net.UDPConn: ReadFromUDP
// returns (0, nil, syscall.EINVAL) and WriteToUDP (0, syscall.EINVAL), each
// the bare Errno (err == syscall.EINVAL, not wrapped in an *OpError): c.ok()
// is false (c.fd == nil), and readFromUDP and WriteToUDP return
// syscall.EINVAL first (net/udpsock.go). (Close, promoted from conn, does the
// same, net/net.go, but is not modeled: U12.)
//
// Model: agrees (the models return Go's syscall.EINVAL for the id 0).
func TestUDPZeroValue(t *testing.T) {
	t.Parallel()
	var c net.UDPConn
	n, from, err := c.ReadFromUDP(make([]byte, 8))
	if n != 0 || from != nil || err != syscall.EINVAL {
		t.Fatalf("zero ReadFromUDP: %d, %v, %#v", n, from, err)
	}
	k, err2 := c.WriteToUDP([]byte("x"), &net.UDPAddr{IP: net.IP{127, 0, 0, 1}, Port: udpPortLo})
	if k != 0 || err2 != syscall.EINVAL {
		t.Fatalf("zero WriteToUDP: %d, %#v", k, err2)
	}
	evidence(t, "U9", fmt.Sprintf("zero UDPConn: ReadFromUDP (0, nil, %T %d), WriteToUDP (0, %T %d): bare",
		err, err, err2, err2), "allowed (the models' id-0 check)")
}
