package shutdown

import (
	"net"
	"testing"
	"time"
)

// TestRun runs Run, then checks that it closed its listener (the address can
// be listened at again).
func TestRun(t *testing.T) {
	Run()
	l, err := net.Listen("tcp", Addr)
	if err != nil {
		t.Fatalf("Run left its listener open: %v", err)
	}
	l.Close()
}

// TestBlockedAccept checks Go's behavior Run relies on with the Accept
// certainly blocked when the listener is closed: it returns an error.
func TestBlockedAccept(t *testing.T) {
	l, err := net.Listen("tcp", Addr)
	if err != nil {
		t.Fatal(err)
	}
	done := make(chan error)
	go func() {
		_, err := l.Accept()
		done <- err
	}()
	time.Sleep(50 * time.Millisecond)
	l.Close()
	if err := <-done; err == nil {
		t.Fatal("a blocked Accept succeeded after Close")
	}
}

// TestBlockedRead: a Read blocked when another goroutine closes the
// connection returns an error.
func TestBlockedRead(t *testing.T) {
	l, err := net.Listen("tcp", Addr)
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	c, err := net.Dial("tcp", Addr)
	if err != nil {
		t.Fatal(err)
	}
	s, err := l.Accept()
	if err != nil {
		t.Fatal(err)
	}
	defer s.Close()
	done := make(chan error)
	go func() {
		_, err := c.Read(make([]byte, 1))
		done <- err
	}()
	time.Sleep(50 * time.Millisecond)
	closeConn(c)
	if err := <-done; err == nil {
		t.Fatal("a blocked Read succeeded after Close")
	}
}
