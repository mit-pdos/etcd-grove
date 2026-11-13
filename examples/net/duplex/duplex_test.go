package duplex

import (
	"io"
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

func TestCall(t *testing.T) {
	startServer(t)
	for i := 0; i < 20; i++ {
		Call()
	}
}

// TestServerEcho checks the server's echo directly: one large write, read
// back in pieces of whatever size arrives.
func TestServerEcho(t *testing.T) {
	startServer(t)
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	msg := make([]byte, 1000)
	for i := range msg {
		msg[i] = byte(i)
	}
	go c.Write(msg)
	resp := make([]byte, len(msg))
	if _, err := io.ReadFull(c, resp); err != nil {
		t.Fatal(err)
	}
	if string(resp) != string(msg) {
		t.Fatal("the echo differs from the bytes written")
	}
}
