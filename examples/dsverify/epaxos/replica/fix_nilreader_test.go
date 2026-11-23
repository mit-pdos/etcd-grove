package replica

import (
	"bufio"
	"bytes"
	"encoding/binary"
	"io"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos-epaxos/replica/defs"
)

// TestConnectToPeersMissingPeer: replica 0 of 2 waits for peer 1; the one connection of its
// peer phase breaks before its handshake (the peer phase counts it, as it always did). Then
// ConnectToPeers returns with no connection to peer 1: it must not start a listener on peer 1's
// missing reader (a nil *bufio.Reader: nil dereference in replicaListener). Peer 1 connecting
// later is then served as a peer.
func TestConnectToPeersMissingPeer(t *testing.T) {
	r := newListeningReplica(t, 2)
	returned := make(chan bool)
	go func() {
		r.ConnectToPeers()
		returned <- true
	}()
	broken := dialReplica(t, r)
	broken.Close()
	<-returned
	go r.WaitForClientConnections()

	peer1 := dialReplica(t, r)
	defer peer1.Close()
	w := bufio.NewWriter(peer1)
	var id [4]byte
	binary.LittleEndian.PutUint32(id[:], 1)
	w.Write(id[:])
	w.WriteByte(defs.GENERIC_SMR_BEACON)
	(&defs.Beacon{Timestamp: 43}).Marshal(w)
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
	if rep[0] != defs.GENERIC_SMR_BEACON_REPLY || br.Timestamp != 43 {
		t.Fatalf("reply %v", rep)
	}
}
