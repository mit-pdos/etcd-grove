//go:build linux

package semantics

import (
	"errors"
	"fmt"
	"net"
	"os"
	"testing"
)

// TestUDPKilledProcess (U7, U5; Lean: udp_semantics.crash, UdpLocal.init,
// RecvStep). A child process binds a UDP address and never reads; the parent
// sends it three datagrams and waits until they are queued at the child's
// socket (rx_queue of its line in /proc/net/udp, read without touching the
// socket), then kills it with SIGKILL and reaps it (do_exit closes its files,
// so the socket is gone). Measured: the socket's line is gone from
// /proc/net/udp; the parent's ListenUDP of the same address succeeds; the
// new socket receives none of the three queued datagrams (a read bounded by
// the harness's deadline times out), and does receive a datagram sent after
// it was bound. Why: the queued datagrams were in the dead socket's receive
// queue, freed with it (udp_destroy_sock, skb_queue_purge).
//
// Model: agrees with the crash (the node's sockets are gone, a new bind is a
// new socket), and over-approximates the network: the three datagrams stay in
// UdpGlobal.sent, so the model lets the new socket receive them, which Linux
// never does (U5: more behaviours than Linux, sound).
func TestUDPKilledProcess(t *testing.T) {
	t.Parallel()
	a := udpFreeAddr(t, "127.0.0.1")
	ch := startUDPChild(t, "bind", a.String())
	if l := ch.line(t); l != "ready" {
		t.Fatalf("child: %q", l)
	}
	s := udpListen(t, "127.0.0.1")
	q, _ := procUDPQueue(t, a)
	for i := 0; i < 3; i++ {
		prev := q
		udpSend(t, s, []byte(fmt.Sprintf("queued-%d", i)), a)
		// rx_queue is the receive queue's memory charge: it grows with each datagram queued.
		waitFor(t, "the datagram queued at the child's socket", func() bool {
			var ok bool
			q, ok = procUDPQueue(t, a)
			return ok && q > prev
		})
	}
	ch.kill(t)
	if _, ok := procUDPQueue(t, a); ok {
		t.Fatalf("the killed child's socket at %v is still in /proc/net/udp", a)
	}
	forkMu.RLock()
	r, err := net.ListenUDP("udp4", a)
	forkMu.RUnlock()
	if err != nil {
		t.Fatalf("ListenUDP(%v) after the child's death: %s", a, udpShape(err))
	}
	defer r.Close()
	_, _, err = udpRecv(r, 64, udpShort)
	if !errors.Is(err, os.ErrDeadlineExceeded) {
		t.Fatalf("new socket's first read: %s (want nothing: the queued datagrams died with the child)", udpShape(err))
	}
	udpSend(t, s, []byte("fresh"), a)
	if b, _, err := udpRecv(r, 64, guard); err != nil || string(b) != "fresh" {
		t.Fatalf("new socket: %q, %v", b, err)
	}
	evidence(t, "U7,U5", fmt.Sprintf("child killed with rx_queue %d (3 datagrams queued): its socket gone, rebind ok, none of the 3 received, a fresh one is", q),
		"allowed (crash drops the sockets); the model also allows receiving the 3 (over-approximation)")
}
