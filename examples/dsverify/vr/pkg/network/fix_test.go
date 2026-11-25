package network

import (
	"bytes"
	"errors"
	"net"
	"runtime"
	"testing"
	"time"

	"github.com/tangledbytes/go-vsr/pkg/events"
	"github.com/tangledbytes/go-vsr/pkg/ipv4port"
)

// scriptedListener is a net.Listener whose Accept returns the scripted results in order; after
// the last one it ends the accepting goroutine (runtime.Goexit), so that serve's loop stops.
type scriptedListener struct {
	results []acceptResult
}

type acceptResult struct {
	conn net.Conn
	err  error
}

func (l *scriptedListener) Accept() (net.Conn, error) {
	if len(l.results) == 0 {
		runtime.Goexit()
	}
	r := l.results[0]
	l.results = l.results[1:]
	return r.conn, r.err
}

func (l *scriptedListener) Close() error   { return nil }
func (l *scriptedListener) Addr() net.Addr { return &net.TCPAddr{IP: net.IPv4(127, 0, 0, 1), Port: 7000} }

// serveScripted runs tcp.serve over the scripted results in its own goroutine and returns the
// panic value, if serve panicked (nil once the script is done).
func serveScripted(tcp *TCP, results ...acceptResult) any {
	done := make(chan any, 1)
	go func() {
		var p any
		defer func() { done <- p }()
		defer func() { p = recover() }()
		tcp.serve(&scriptedListener{results: results})
	}()
	return <-done
}

func recvWithin(tcp *TCP, d time.Duration) (events.NetworkEvent, bool) {
	deadline := time.Now().Add(d)
	for time.Now().Before(deadline) {
		if ev, ok := tcp.Recv(); ok {
			return ev, true
		}
		time.Sleep(time.Millisecond)
	}
	return events.NetworkEvent{}, false
}

// K1: a failed Accept returns a nil Conn (Go's net docs); the listener must go on accepting and
// the connections it accepts afterwards must deliver their events.
func TestFixK1FailedAcceptDoesNotStopTheListener(t *testing.T) {
	tcp := NewTCP("127.0.0.1:7000")
	server, client := net.Pipe()
	defer client.Close()
	p := serveScripted(tcp,
		acceptResult{nil, errors.New("accept: too many open files")},
		acceptResult{server, nil})
	if p != nil {
		t.Fatalf("K1: the accept loop panicked after a failed Accept (%v): it used the nil Conn", p)
	}
	go (&events.Event{Type: events.EventRequest, Data: events.Request{ID: 1, ClientID: 1, Op: "x"}}).ToWriter(client)
	if _, ok := recvWithin(tcp, 5*time.Second); !ok {
		t.Fatal("K1: the connection accepted after a failed Accept delivered no event")
	}
}

// J1: the network delivers one event per JSON value on a connection. Two events that arrive in
// one read (one Write of both: TCP does not keep message boundaries) must both be delivered, in
// order; a fresh json.Decoder per event drops the bytes the previous one read ahead.
func TestFixJ1EventsSharingAReadAreAllDelivered(t *testing.T) {
	tcp := NewTCP("127.0.0.1:7000")
	server, client := net.Pipe()
	defer client.Close()
	if p := serveScripted(tcp, acceptResult{server, nil}); p != nil {
		t.Fatalf("accept loop panicked: %v", p)
	}
	var buf bytes.Buffer
	for id := uint64(1); id <= 2; id++ {
		ev := events.Event{Type: events.EventRequest, Data: events.Request{ID: id, ClientID: 7, Op: "SET k v"}}
		if err := ev.ToWriter(&buf); err != nil {
			t.Fatal(err)
		}
	}
	go client.Write(buf.Bytes())
	for id := uint64(1); id <= 2; id++ {
		ev, ok := recvWithin(tcp, 3*time.Second)
		if !ok {
			t.Fatalf("J1: event %d of 2 written on the connection was never delivered (lost with a dropped decoder's read-ahead)", id)
		}
		if req, _ := ev.Event.Data.(events.Request); req.ID != id {
			t.Fatalf("J1: event %d delivered as %+v", id, ev.Event.Data)
		}
	}
}

// failingConn is a net.Conn whose Write writes a prefix of its argument (recorded) and fails;
// its Read blocks until it is closed.
type failingConn struct {
	writes  int
	written []byte
	closed  chan struct{}
}

func newFailingConn() *failingConn { return &failingConn{closed: make(chan struct{})} }

func (c *failingConn) Write(b []byte) (int, error) {
	c.writes++
	n := len(b) / 2
	c.written = append(c.written, b[:n]...)
	return n, &net.OpError{Op: "write", Net: "tcp", Err: errors.New("connection reset by peer")}
}

func (c *failingConn) Read(b []byte) (int, error) {
	<-c.closed
	return 0, net.ErrClosed
}

func (c *failingConn) Close() error {
	select {
	case <-c.closed:
	default:
		close(c.closed)
	}
	return nil
}

func (c *failingConn) LocalAddr() net.Addr                { return &net.TCPAddr{} }
func (c *failingConn) RemoteAddr() net.Addr               { return &net.TCPAddr{} }
func (c *failingConn) SetDeadline(t time.Time) error      { return nil }
func (c *failingConn) SetReadDeadline(t time.Time) error  { return nil }
func (c *failingConn) SetWriteDeadline(t time.Time) error { return nil }

// N1b: the network sends each event as one JSON value on a connection. After a write failed
// part-way, the stream may end in part of an event: nothing written after it can be framed, so
// the connection must not be used again; the next Send to the address goes on a new connection,
// where the event arrives whole.
func TestFixN1bFailedConnectionIsNotReused(t *testing.T) {
	l, err := net.Listen("tcp4", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	var peer ipv4port.IPv4Port
	if err := peer.FromHostPort(l.Addr().String()); err != nil {
		t.Fatal(err)
	}
	tcp := NewTCP("127.0.0.1:7000")
	bad := newFailingConn()
	tcp.conns[peer.String()] = bad // the connection to peer, dialed earlier
	send := func(id uint64) error {
		return tcp.Send(peer, (&events.Event{Type: events.EventRequest, Data: events.Request{ID: id, ClientID: 1, Op: "SET k v"}}).ToWriter)
	}
	if send(1) == nil {
		t.Fatal("the failed write was not reported")
	}
	accepted := make(chan net.Conn, 1)
	go func() {
		c, err := l.Accept()
		if err == nil {
			accepted <- c
		}
	}()
	err = send(2)
	if bad.writes > 1 {
		t.Fatalf("N1b: event 2 was written on the connection whose write of event 1 failed part-way: the stream now holds %q, which no reader can frame", bad.written)
	}
	if err != nil {
		t.Fatalf("send on a new connection: %v", err)
	}
	select {
	case c := <-accepted:
		defer c.Close()
		var ev events.Event
		if err := ev.FromReader(c); err != nil {
			t.Fatalf("N1b: the event on the new connection does not decode: %v", err)
		}
		if req := ev.Data.(events.Request); req.ID != 2 {
			t.Fatalf("N1b: got %+v on the new connection", req)
		}
	case <-time.After(5 * time.Second):
		t.Fatal("N1b: no new connection was dialed for event 2")
	}
}
