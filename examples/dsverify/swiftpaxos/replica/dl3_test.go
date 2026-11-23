package replica

import (
	"io"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos/replica/defs"
	fastrpc "github.com/imdea-software/swiftpaxos/rpc"
)

type dl3Msg struct{}

func (*dl3Msg) Marshal(w io.Writer) { w.Write([]byte{0}) }
func (*dl3Msg) Unmarshal(r io.Reader) error {
	var b [1]byte
	_, err := io.ReadFull(r, b[:])
	return err
}
func (*dl3Msg) New() fastrpc.Serializable { return new(dl3Msg) }

// DL3: a peer slot whose connection failed (here: a connection that closes
// before its handshake takes replica 1's slot) has no reader: ConnectToPeers
// must not start a reader on it, and the senders must skip it.
func TestIssueDL3_NoReaderForMissingPeer(t *testing.T) {
	addrs := freeAddrs(t, 2)
	r0 := newTestReplica(0, addrs)
	peersDone := make(chan struct{})
	go func() {
		r0.ConnectToPeers()
		close(peersDone)
	}()
	c := dialRetry(t, addrs[0])
	c.Close() // no handshake byte: the slot is consumed, no peer
	select {
	case <-peersDone:
	case <-time.After(10 * time.Second):
		t.Fatal("replica 0 did not finish connecting to its peers")
	}
	time.Sleep(200 * time.Millisecond) // a reader for peer 1, if started, has run

	r0.M.Lock()
	alive := r0.Alive[1]
	r0.M.Unlock()
	if alive || r0.PeerReaders[1] != nil {
		t.Fatalf("peer 1 alive=%v reader=%v, want not alive, no reader", alive, r0.PeerReaders[1])
	}
	// The send paths with the missing peer: no panic.
	msg := &dl3Msg{}
	r0.SendMsg(1, defs.RPC_TABLE, msg)
	r0.SendMsgNoFlush(1, defs.RPC_TABLE, msg)
	r0.SendBeacon(1)
	r0.ReplyBeacon(&defs.GBeacon{Rid: 1, Timestamp: 1})
	sendToAll(r0, msg, defs.RPC_TABLE)
	sendToAllExcept(r0, 0, msg, defs.RPC_TABLE)
}
