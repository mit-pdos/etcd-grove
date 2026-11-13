package preface

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

// TestJunkThenCall: a client that stops halfway through its preface holds the
// server only until the deadline (Call runs after it).
func TestJunkThenCall(t *testing.T) {
	startServer(t)
	start := time.Now()
	SendJunk()
	if d := time.Since(start); d > 5*time.Second {
		t.Fatalf("the server held the junk connection for %v", d)
	}
	Call()
}

// TestWrongPreface: the server closes a connection with a wrong preface
// without replying.
func TestWrongPreface(t *testing.T) {
	startServer(t)
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	if _, err := c.Write([]byte("JUNK?")); err != nil {
		t.Fatal(err)
	}
	resp, _ := io.ReadAll(c)
	if len(resp) != 0 {
		t.Fatalf("reply %q to a wrong preface", resp)
	}
	Call()
}

// TestDeadlineCleared: after the preface, the request may come later than the
// deadline would have allowed.
func TestDeadlineCleared(t *testing.T) {
	startServer(t)
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	if _, err := c.Write([]byte(Magic)); err != nil {
		t.Fatal(err)
	}
	time.Sleep(1500 * time.Millisecond)
	if _, err := c.Write([]byte{7}); err != nil {
		t.Fatal(err)
	}
	resp := make([]byte, 1)
	if _, err := io.ReadFull(c, resp); err != nil {
		t.Fatal(err)
	}
	if resp[0] != 7 {
		t.Fatalf("reply %d, want 7", resp[0])
	}
}
