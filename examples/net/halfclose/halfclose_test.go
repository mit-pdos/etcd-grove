package halfclose

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
	Call()
}

// TestServerReadsUntilEOF checks the server directly: a request of several
// writes larger than its read buffer comes back whole, then EOF.
func TestServerReadsUntilEOF(t *testing.T) {
	startServer(t)
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	req := "a request of several writes, longer than the server's buffer"
	for i := 0; i < len(req); i += 7 {
		if _, err := c.Write([]byte(req[i:min(i+7, len(req))])); err != nil {
			t.Fatal(err)
		}
	}
	if err := c.(*net.TCPConn).CloseWrite(); err != nil {
		t.Fatal(err)
	}
	resp, err := io.ReadAll(c)
	if err != nil {
		t.Fatal(err)
	}
	if string(resp) != req {
		t.Fatalf("response %q, want %q", resp, req)
	}
}

// TestJunkClient: a client that closes at once, then one that sends nothing,
// do not stop the server from serving the next.
func TestJunkClient(t *testing.T) {
	startServer(t)
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		t.Fatal(err)
	}
	c.Close()
	c, err = net.Dial("tcp", SrvAddr)
	if err != nil {
		t.Fatal(err)
	}
	c.(*net.TCPConn).CloseWrite()
	io.ReadAll(c)
	c.Close()
	Call()
}
