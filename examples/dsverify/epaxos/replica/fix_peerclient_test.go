package replica

import (
	"bufio"
	"bytes"
	"encoding/binary"
	"fmt"
	"io"
	"net"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos-epaxos/config"
	"github.com/imdea-software/swiftpaxos-epaxos/dlog"
	"github.com/imdea-software/swiftpaxos-epaxos/replica/defs"
	"github.com/imdea-software/swiftpaxos-epaxos/state"
)

// newListeningReplica is replica 0 of n, whose own address is a free loopback port (it is not
// listening yet: waitForPeerConnections listens on it).
func newListeningReplica(t *testing.T, n int) *Replica {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	addrs := []string{l.Addr().String()}
	l.Close()
	for i := 1; i < n; i++ {
		addrs = append(addrs, fmt.Sprintf("127.0.0.1:%d", 1+i)) // never dialed: replica 0 dials no peer
	}
	return New("n0", 0, 1, addrs, false, true, false, &config.Config{Proxy: &config.ProxyInfo{}}, &dlog.Logger{})
}

// dialReplica connects to r once its listener is up. The replica's kernel queues the
// connections in the order this test makes them, and its Accept takes them in that order.
func dialReplica(t *testing.T, r *Replica) net.Conn {
	for i := 0; i < 1000; i++ {
		if c, err := net.Dial("tcp", r.PeerAddrList[r.Id]); err == nil {
			return c
		}
		time.Sleep(10 * time.Millisecond)
	}
	t.Fatal("replica does not listen")
	return nil
}

// sendProposal writes what the kit's client (Op) writes: PROPOSE and a defs.Propose.
func sendProposal(t *testing.T, c net.Conn, clientId int32, v string) {
	w := bufio.NewWriter(c)
	w.WriteByte(defs.PROPOSE)
	p := defs.Propose{CommandId: 0, ClientId: clientId,
		Command: state.Command{Op: state.PUT, K: 1, V: state.Value([]byte(v))}}
	p.Marshal(w)
	if err := w.Flush(); err != nil {
		t.Fatal(err)
	}
}

// sendPeerId writes a peer's handshake: its id, 4 bytes little-endian (ConnectToPeers).
func sendPeerId(t *testing.T, c net.Conn, id uint32) {
	var b [4]byte
	binary.LittleEndian.PutUint32(b[:], id)
	if _, err := c.Write(b[:]); err != nil {
		t.Fatal(err)
	}
}

func peerSlot(r *Replica, id int) net.Conn {
	r.M.Lock()
	defer r.M.Unlock()
	return r.Peers[id]
}

// TestClientInPeerPhase: replica 0 of 3 waits for its 2 peers (1 and 2); a client connects
// and proposes first, then peer 1 connects. The client's connection must be served as a
// client's (its proposal reaches ProposeChan) and must not take a peer slot (P1: its bytes
// PROPOSE, CommandId 0 were read as peer id 0).
func TestClientInPeerPhase(t *testing.T) {
	r := newListeningReplica(t, 3)
	done := make(chan bool)
	go r.waitForPeerConnections(done)

	client := dialReplica(t, r)
	defer client.Close()
	sendProposal(t, client, 5, "v50")
	peer1 := dialReplica(t, r)
	defer peer1.Close()
	sendPeerId(t, peer1, 1)
	<-done // after 2 accepts, as before

	if peerSlot(r, 0) != nil {
		t.Fatal("the client's connection took peer slot 0")
	}
	if peerSlot(r, 1) == nil {
		t.Fatal("peer 1 is not registered")
	}
	select {
	case p := <-r.ProposeChan:
		if p.ClientId != 5 || string(p.Command.V) != "v50" {
			t.Fatalf("proposal %+v", p.Propose)
		}
	case <-time.After(10 * time.Second):
		t.Fatal("the client's proposal never reached ProposeChan")
	}
}

// TestPeerAfterPeerPhase: replica 0 of 2 waits for one peer; a client connects first (the
// peer phase's one accept), then peer 1 connects, accepted by WaitForClientConnections. Peer 1
// must be registered and served as a peer (its beacon is answered on its connection), not
// parsed as a client (P1: its id bytes were read as client message types).
func TestPeerAfterPeerPhase(t *testing.T) {
	r := newListeningReplica(t, 2)
	done := make(chan bool)
	go r.waitForPeerConnections(done)

	client := dialReplica(t, r)
	defer client.Close()
	sendProposal(t, client, 7, "v70")
	<-done // after 1 accept, as before
	go r.WaitForClientConnections()

	peer1 := dialReplica(t, r)
	defer peer1.Close()
	w := bufio.NewWriter(peer1)
	var id [4]byte
	binary.LittleEndian.PutUint32(id[:], 1)
	w.Write(id[:])
	w.WriteByte(defs.GENERIC_SMR_BEACON)
	(&defs.Beacon{Timestamp: 42}).Marshal(w)
	if err := w.Flush(); err != nil {
		t.Fatal(err)
	}

	peer1.SetReadDeadline(time.Now().Add(10 * time.Second)) // only a failing run waits
	var rep [9]byte
	if _, err := io.ReadFull(peer1, rep[:]); err != nil {
		t.Fatalf("no beacon reply to peer 1: %v", err)
	}
	var br defs.BeaconReply
	br.Unmarshal(bytes.NewReader(rep[1:]))
	if rep[0] != defs.GENERIC_SMR_BEACON_REPLY || br.Timestamp != 42 {
		t.Fatalf("reply %v", rep)
	}
	if peerSlot(r, 1) == nil {
		t.Fatal("peer 1 is not registered")
	}
}
