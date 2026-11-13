package acceptloop

import (
	"net"
	"sync"
	"testing"
	"time"
)

var srvOnce sync.Once

// startServer runs Serve in the background (once per process: it never
// returns) and waits until it accepts connections.
func startServer(t *testing.T) {
	t.Helper()
	srvOnce.Do(func() { go Serve() })
	deadline := time.Now().Add(5 * time.Second)
	for {
		c, err := net.Dial("tcp", SrvAddr)
		if err == nil {
			c.Close()
			return
		}
		if time.Now().After(deadline) {
			t.Fatalf("server not listening at %s: %v", SrvAddr, err)
		}
		time.Sleep(10 * time.Millisecond)
	}
}

// TestCall runs Call (whose goroutines a panic would fail the test binary
// from), then many concurrent CallOnes, waiting for them.
func TestCall(t *testing.T) {
	startServer(t)
	Call()
	var wg sync.WaitGroup
	for i := 1; i <= 50; i++ {
		wg.Add(1)
		go func(id byte) {
			defer wg.Done()
			CallOne(id)
		}(byte(i))
	}
	wg.Wait()
}

// TestIdleClient checks that a connection that sends nothing does not hold
// up the others (the accept loop does not wait for a handler).
func TestIdleClient(t *testing.T) {
	startServer(t)
	idle, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		t.Fatal(err)
	}
	defer idle.Close()
	CallOne(7)
	CallOne(8)
}
