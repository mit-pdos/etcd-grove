package replica

import (
	"net"
	"strings"
	"testing"
	"time"
)

// waitForPeerConnections on a failed net.Listen: with the non-verbose logger
// Fatal returns, and r.Listener must not stay nil (the peer loop and
// WaitForClientConnections call Accept on it); it must listen once the port
// is free.
func TestIssueReplicaListen_RetryOnListenError(t *testing.T) {
	busy, err := net.Listen("tcp", "0.0.0.0:0")
	if err != nil {
		t.Fatal(err)
	}
	port := busy.Addr().String()[strings.LastIndex(busy.Addr().String(), ":"):]
	r := newTestReplica(0, []string{"127.0.0.1" + port})
	done := make(chan bool, 1)
	panicked := make(chan any, 1)
	go func() {
		defer func() { panicked <- recover() }()
		r.waitForPeerConnections(done)
	}()
	time.Sleep(300 * time.Millisecond) // the first Listen fails: the port is taken
	busy.Close()

	select {
	case <-done:
	case p := <-panicked:
		t.Fatalf("waitForPeerConnections panicked: %v", p)
	case <-time.After(5 * time.Second):
		t.Fatal("waitForPeerConnections never finished")
	}
	if r.Listener == nil {
		t.Fatal("r.Listener is nil after waitForPeerConnections")
	}
	c, err := net.Dial("tcp", "127.0.0.1"+port)
	if err != nil {
		t.Fatalf("nothing listens on the replica's port: %v", err)
	}
	c.Close()
	r.Listener.Close()
}
