package replica

import (
	"net"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos-epaxos/config"
	"github.com/imdea-software/swiftpaxos-epaxos/dlog"
)

// TestPeerListenRetry: replica 0 of 2's address is in use when it starts listening, so its
// first Listen fails (r.Fatal does nothing with the non-verbose logger). It must not Accept on
// a nil listener; once the address is free it listens and takes peer 1's connection.
func TestPeerListenRetry(t *testing.T) {
	occupied, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	addrs := []string{occupied.Addr().String(), "127.0.0.1:2"}
	r := New("n0", 0, 0, addrs, false, true, false, &config.Config{Proxy: &config.ProxyInfo{}}, &dlog.Logger{})
	done := make(chan bool)
	go r.waitForPeerConnections(done)
	// Let the first Listen run while the address is in use (only the run before the fix
	// depends on this: it then panics).
	time.Sleep(100 * time.Millisecond)
	occupied.Close()

	peer1 := dialReplica(t, r)
	defer peer1.Close()
	sendPeerId(t, peer1, 1)
	<-done
	if peerSlot(r, 1) == nil {
		t.Fatal("peer 1 is not registered")
	}
}
