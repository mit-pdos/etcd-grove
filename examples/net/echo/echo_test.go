package echo

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
	Call()
}

func TestJunkThenCall(t *testing.T) {
	startServer(t)
	SendJunk()
	Call()
	SendJunk()
	Call()
}

// TestServerSplitRequest checks the server directly: a request written one
// byte at a time comes back whole.
func TestServerSplitRequest(t *testing.T) {
	startServer(t)
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	req := []byte("abcde")
	for i := range req {
		if _, err := c.Write(req[i : i+1]); err != nil {
			t.Fatal(err)
		}
	}
	resp := make([]byte, reqLen)
	if _, err := io.ReadFull(c, resp); err != nil {
		t.Fatal(err)
	}
	if string(resp) != string(req) {
		t.Fatalf("reply %q, want %q", resp, req)
	}
}
