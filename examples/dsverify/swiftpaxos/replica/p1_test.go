package replica

import (
	"bufio"
	"net"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos/config"
	"github.com/imdea-software/swiftpaxos/dlog"
	"github.com/imdea-software/swiftpaxos/replica/defs"
	"github.com/imdea-software/swiftpaxos/state"
)

func freeAddrs(t *testing.T, n int) []string {
	addrs := make([]string, n)
	for i := range addrs {
		l, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatal(err)
		}
		addrs[i] = l.Addr().String()
		l.Close()
	}
	return addrs
}

func newTestReplica(id int, addrs []string) *Replica {
	return New("", id, 0, addrs, false, true, false,
		&config.Config{Proxy: &config.ProxyInfo{}}, &dlog.Logger{})
}

func dialRetry(t *testing.T, addr string) net.Conn {
	for i := 0; i < 100; i++ {
		if c, err := net.Dial("tcp", addr); err == nil {
			return c
		}
		time.Sleep(50 * time.Millisecond)
	}
	t.Fatalf("cannot dial %s", addr)
	return nil
}

// P1: peers and clients share the replica's port. A client that connects
// before the peer (here: accepted first) must not be taken as the peer, and
// the peer must not be taken as a client.
func TestIssueP1_ClientBeforePeer(t *testing.T) {
	addrs := freeAddrs(t, 2)
	r0, r1 := newTestReplica(0, addrs), newTestReplica(1, addrs)

	peersDone := make(chan struct{})
	go func() {
		r0.ConnectToPeers()
		close(peersDone)
	}()

	// The client connects and sends its first proposal (CommandId 0: its
	// first bytes are 0 0 0 0).
	cc := dialRetry(t, addrs[0])
	defer cc.Close()
	w := bufio.NewWriter(cc)
	w.WriteByte(defs.PROPOSE)
	(&defs.Propose{CommandId: 0, ClientId: 7,
		Command: state.Command{Op: state.PUT, K: 1, V: state.Value("v")}}).Marshal(w)
	w.Flush()
	time.Sleep(200 * time.Millisecond)

	// Then the peer, replica 1, connects as replicas do.
	go r1.ConnectToPeers()

	select {
	case <-peersDone:
	case <-time.After(10 * time.Second):
		t.Fatal("replica 0 did not finish connecting to its peers")
	}
	if r0.Peers[0] != nil || r0.Peers[1] == nil || !r0.Alive[1] {
		t.Fatalf("replica 0's peers: %v (alive %v), want only replica 1", r0.Peers, r0.Alive)
	}

	go r0.WaitForClientConnections()
	select {
	case p := <-r0.ProposeChan:
		if p.ClientId != 7 || p.CommandId != 0 || string(p.Command.V) != "v" {
			t.Fatalf("proposal %+v, want the client's", p.Propose)
		}
	case <-time.After(10 * time.Second):
		t.Fatal("the client's proposal never reached replica 0")
	}
}

// P1: a peer handshake with an id out of range (bytes off the wire) must not
// index past r.Peers.
func TestIssueP1_OutOfRangePeerId(t *testing.T) {
	addrs := freeAddrs(t, 2)
	r0 := newTestReplica(0, addrs)
	// waitForPeerConnections only: ConnectToPeers would then start a reader
	// for the peer that never connected (a nil reader; not P1).
	peersDone := make(chan bool, 1)
	go r0.waitForPeerConnections(peersDone)
	c := dialRetry(t, addrs[0])
	defer c.Close()
	c.Write([]byte{0xFF, 0xE8, 0x03, 0x00, 0x00})
	select {
	case <-peersDone:
	case <-time.After(10 * time.Second):
		t.Fatal("replica 0 did not finish connecting to its peers")
	}
	for i, p := range r0.Peers {
		if p != nil {
			t.Fatalf("peer %d set from a bad handshake", i)
		}
	}
}
