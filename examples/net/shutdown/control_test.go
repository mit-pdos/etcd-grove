package shutdown

import (
	"net"
	"sync"
	"testing"
)

// recConn is a net.Conn that records the methods called on it, in order; with
// lax, its operations after a Close succeed (a mutant of Go's guarantee).
type recConn struct {
	net.Conn
	mu     sync.Mutex
	calls  []string
	closed bool
	lax    bool
}

func (c *recConn) record(m string) bool {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.calls = append(c.calls, m)
	return c.closed && c.lax
}

func (c *recConn) Write(b []byte) (int, error) {
	if c.record("Write") {
		return len(b), nil
	}
	return c.Conn.Write(b)
}

func (c *recConn) Read(b []byte) (int, error) {
	if c.record("Read") {
		return len(b), nil
	}
	return c.Conn.Read(b)
}

func (c *recConn) Close() error {
	if c.record("Close") {
		return nil
	}
	err := c.Conn.Close()
	c.mu.Lock()
	c.closed = true
	c.mu.Unlock()
	return err
}

// listenDial makes Run's setup: a listener at Addr with acceptLoop, and a
// connection dialed to it.
func listenDial(t *testing.T) (net.Listener, net.Conn) {
	t.Helper()
	l, err := net.Listen("tcp", Addr)
	if err != nil {
		t.Fatal(err)
	}
	go acceptLoop(l)
	c, err := net.Dial("tcp", Addr)
	if err != nil {
		l.Close()
		t.Fatalf("Dial of the node's own listener failed (Run would skip its connection checks): %v", err)
	}
	return l, c
}

// TestConnChecksRun shows that Run's connection checks are reached: its Dial
// of its own listener succeeds (on the target configuration a Dial of a live
// loopback listener does), so Run goes on to closeConn, which closes the
// connection, then makes the Write, the Read and the second Close it checks;
// all three fail, as Go guarantees, so nothing panics. (Run's own steps, made
// here one by one so that they can be observed.)
func TestConnChecksRun(t *testing.T) {
	l, c := listenDial(t)
	defer l.Close()
	go readLoop(c)
	rc := &recConn{Conn: c}
	if panics(func() { closeConn(rc) }) {
		t.Fatal("closeConn panicked on a real connection")
	}
	want := []string{"Close", "Write", "Read", "Close"}
	if len(rc.calls) != len(want) {
		t.Fatalf("closeConn made %v, want %v", rc.calls, want)
	}
	for i := range want {
		if rc.calls[i] != want[i] {
			t.Fatalf("closeConn made %v, want %v", rc.calls, want)
		}
	}
	l.Close()
	if _, err := l.Accept(); err == nil {
		t.Fatal("an Accept after Close succeeded")
	}
}

// TestCheckFires is the negative control of the connection checks: on a
// connection whose operations after a Close succeed (a mutant of Go's
// guarantee), closeConn panics. The checks can fail, so the robustness
// theorem's "no thread panics" excludes something.
func TestCheckFires(t *testing.T) {
	l, c := listenDial(t)
	defer l.Close()
	defer c.Close()
	if !panics(func() { closeConn(&recConn{Conn: c, lax: true}) }) {
		t.Fatal("closeConn did not panic on a connection whose Write after Close succeeds")
	}
}

// panics reports whether f panics.
func panics(f func()) (p bool) {
	defer func() {
		if recover() != nil {
			p = true
		}
	}()
	f()
	return false
}
