package master

import (
	"fmt"
	"net"
	"net/rpc"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos/config"
	"github.com/imdea-software/swiftpaxos/dlog"
	"github.com/imdea-software/swiftpaxos/replica/defs"
)

// Run on a failed net.Listen: with the non-verbose logger Fatal returns, and
// Run must not serve a nil listener (http.Serve panics on it); it must start
// serving once the port is free.
func TestIssueMasterListen_RetryOnListenError(t *testing.T) {
	busy, err := net.Listen("tcp", ":0")
	if err != nil {
		t.Fatal(err)
	}
	port := busy.Addr().(*net.TCPAddr).Port
	m := New(1, port, &config.Config{}, &dlog.Logger{})
	panicked := make(chan any, 1)
	go func() {
		defer func() { panicked <- recover() }()
		m.Run()
	}()
	time.Sleep(300 * time.Millisecond) // Run's first Listen fails: the port is taken
	busy.Close()

	deadline := time.Now().Add(5 * time.Second)
	for {
		select {
		case p := <-panicked:
			t.Fatalf("master.Run returned or panicked after a failed Listen: %v", p)
		default:
		}
		c, err := rpc.DialHTTP("tcp", fmt.Sprintf("127.0.0.1:%d", port))
		if err == nil {
			var reply defs.GetLeaderReply
			err = c.Call("Master.GetLeader", &defs.GetLeaderArgs{}, &reply)
			c.Close()
			if err != nil {
				t.Fatalf("GetLeader: %v", err)
			}
			return
		}
		if time.Now().After(deadline) {
			t.Fatalf("the master never served after its port became free: %v", err)
		}
		time.Sleep(50 * time.Millisecond)
	}
}
