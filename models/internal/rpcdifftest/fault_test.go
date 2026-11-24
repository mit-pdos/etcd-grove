package rpcdifftest_test

import (
	"errors"
	"fmt"
	"io"
	"net"
	"net/rpc"
	"reflect"
	"sort"
	"strings"
	"sync"
	"syscall"
	"testing"
	"time"

	difftest "models.lab/internal/rpcdifftest"
)

// Values gob merges into a non-zero reply, and the reply kinds the server makes (an empty
// slice), and a method that takes its argument by value: the same results in both builds.
func TestDeepValues(t *testing.T) {
	c := dial(t)
	defer c.Close()
	s := "s"
	in := difftest.Deep{Name: "n", Inner: difftest.Args{A: 1, B: 2}, PStr: &s,
		Items: []difftest.Item{{K: "a", V: 1, W: []uint16{1, 2}}, {}},
		ByKey: map[string]difftest.Item{"x": {K: "y"}, "": {}},
		Raw:   []byte{0, 1}, Flag: true, Small: -3}
	// into a non-zero reply: fields the server's reply leaves zero are not sent, and keep the
	// reply's values; Items reuses the reply's backing array (capacity 4), and its second element
	// (all zero in the argument: no field sent) keeps the stale value there
	old := "old"
	r := difftest.Deep{Name: "keep", PStr: &old, Small: 9, Items: make([]difftest.Item, 4),
		ByKey: map[string]difftest.Item{"z": {V: 5}}}
	r.Items[1] = difftest.Item{K: "stale", V: 7, W: []uint16{9}}
	r.Items = r.Items[:1]
	if err := c.Call("Arith.Swap", &in, &r); err != nil {
		t.Fatal(err)
	}
	got := fmt.Sprintf("%v %v %v %v %v %v %v %v %v", r.Name, r.Inner, *r.Ptr, *r.PStr, r.Items,
		len(r.ByKey), r.Raw, r.Flag, r.Small)
	want := "n {2 1} {2 1} s [{a 1 [1 2]} {stale 7 [9]}] 3 [0 1] true -3"
	if got != want {
		t.Errorf("Swap into a non-zero reply:\n got %s\nwant %s", got, want)
	}
	// a zero argument: nothing sent but the struct
	var z difftest.Deep
	if err := c.Call("Arith.Swap", &difftest.Deep{}, &z); err != nil || z.Ptr == nil ||
		z.Name != "" || z.Items != nil || z.ByKey != nil {
		t.Errorf("Swap of a zero value: %+v %v", z, err)
	}
	var l []difftest.Item
	if err := c.Call("Arith.List", 0, &l); err != nil || l != nil {
		t.Errorf("List(0) into nil: %#v %v (an empty top-level slice decodes into nil as nil)", l, err)
	}
	l2 := []difftest.Item{}
	if err := c.Call("Arith.List", 2, &l2); err != nil || len(l2) != 2 || l2[1].V != 1 {
		t.Errorf("List(2): %#v %v", l2, err)
	}
	var v difftest.Reply
	if err := c.Call("Arith.Value", difftest.Args{A: 6, B: 7}, &v); err != nil || v.C != 42 {
		t.Errorf("Value: %v %v", v, err)
	}
}

// Go (asynchronous calls) and its done channel; a done channel without buffer panics.
func TestGo(t *testing.T) {
	c := dial(t)
	defer c.Close()
	done := make(chan *rpc.Call, 3)
	var rs [3]difftest.Reply
	for i := range rs {
		c.Go("Arith.Add", &difftest.Args{A: uint64(i), B: 1}, &rs[i], done)
	}
	for range rs {
		call := <-done
		if call.Error != nil {
			t.Fatal(call.Error)
		}
	}
	for i := range rs {
		if rs[i].C != uint64(i)+1 {
			t.Errorf("Go %d: %v", i, rs[i])
		}
	}
	func() {
		defer func() {
			if recover() == nil {
				t.Error("Go with an unbuffered done channel did not panic")
			}
		}()
		quiet()
		c.Go("Arith.Add", &difftest.Args{}, &difftest.Reply{}, make(chan *rpc.Call))
	}()
}

// A cutting proxy: it forwards between a client and the server (served by ServeConn on a
// listener of its own, no HTTP), and after `limit` bytes of one direction it stops forwarding
// that direction: closing the whole connection (both), or only that direction's write half
// (half-close: the other direction still flows).
type cutProxy struct {
	addr string
	l    net.Listener
}

func serveRPC(t *testing.T) string {
	srv := rpc.NewServer()
	if err := srv.RegisterName("Arith", arith); err != nil {
		t.Fatal(err)
	}
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { l.Close() })
	go srv.Accept(l)
	return l.Addr().String()
}

// copyN copies at most n bytes (n < 0: all) from src to dst; then, if half, closes dst's write
// side, else closes both connections.
func copyN(dst, src *net.TCPConn, n int64, half bool, done func()) {
	defer done()
	if n >= 0 {
		io.CopyN(dst, src, n)
	} else {
		io.Copy(dst, src)
	}
	if half {
		dst.CloseWrite()
		return
	}
	dst.Close()
	src.Close()
}

// proxyCall dials the server through a proxy that cuts the direction (server to client if
// toClient, else client to server) after n bytes, makes one Add call, and returns its result.
func proxyCall(t *testing.T, server string, n int64, toClient, half bool) error {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	var wg sync.WaitGroup
	go func() {
		a, err := l.Accept()
		if err != nil {
			return
		}
		b, err := net.Dial("tcp", server)
		if err != nil {
			a.Close()
			return
		}
		wg.Add(2)
		ac, bc := a.(*net.TCPConn), b.(*net.TCPConn)
		if toClient {
			go copyN(ac, bc, n, half, wg.Done)
			go copyN(bc, ac, -1, true, wg.Done)
		} else {
			go copyN(bc, ac, n, half, wg.Done)
			go copyN(ac, bc, -1, true, wg.Done)
		}
	}()
	c, err := rpc.Dial("tcp", l.Addr().String())
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	var r difftest.Reply
	errc := make(chan error, 1)
	go func() { errc <- c.Call("Arith.Add", &difftest.Args{A: 1, B: 2}, &r) }()
	select {
	case err := <-errc:
		if err == nil && r.C != 3 {
			return fmt.Errorf("wrong reply %v", r)
		}
		return err
	case <-time.After(10 * time.Second):
		return errors.New("timeout")
	}
}

// describe names an error by what a program can test of it: its type and message.
func describe(err error) string {
	if err == nil {
		return "ok"
	}
	if se, ok := err.(rpc.ServerError); ok {
		return "ServerError(" + string(se) + ")"
	}
	if err == io.ErrUnexpectedEOF {
		return "io.ErrUnexpectedEOF"
	}
	if err == rpc.ErrShutdown {
		return "ErrShutdown"
	}
	return fmt.Sprintf("%T(%s)", err, err.Error())
}

// outcomes cuts the direction at every byte count up to the call's completion and returns the
// set of the call's outcomes (the byte counts differ between the builds: the wire formats differ;
// the outcomes must not).
func outcomes(t *testing.T, toClient, half bool) []string {
	server := serveRPC(t)
	set := map[string]bool{}
	for n := int64(0); ; n++ {
		d := describe(proxyCall(t, server, n, toClient, half))
		set[d] = true
		if d == "ok" {
			break
		}
		if n > 4096 {
			t.Fatalf("no success after %d bytes", n)
		}
	}
	// ErrShutdown is a race, in both builds (the model's Client is Go's code): when the cut comes
	// before the call is registered (n small), the client's reader may see the end of stream and
	// shut the client down before send runs, which then fails the call with ErrShutdown instead of
	// the reader's error. Allowed, not required (measured in both builds, 2026-11-21: one run in
	// ~20 sees it).
	delete(set, "ErrShutdown")
	var out []string
	for d := range set {
		out = append(out, d)
	}
	sort.Strings(out)
	return out
}

// The server's response cut short (the stream to the client ends: a half-close, so that no
// reset races with it): before the response header (or within it) the client
// reads an unexpected end of stream; between the header and the body, reading the body ends
// (gob reads them as two messages, the model as two frames); within the body, an unexpected
// end. The same outcomes in both builds.
func TestCutResponse(t *testing.T) {
	got := strings.Join(outcomes(t, true, true), " ")
	want := "*errors.errorString(reading body EOF) *errors.errorString(reading body unexpected EOF) " +
		"io.ErrUnexpectedEOF ok"
	if got != want {
		t.Errorf("outcomes of a cut response:\n got %s\nwant %s", got, want)
	}
}

// The client's request cut short with the connection half-closed (the server reads an end of
// stream, its responses still flow): within the header, the server stops and closes the
// connection (the call fails with an unexpected end); between the header and the body, or
// within the body, the server answers the request with the body's read error.
func TestCutRequest(t *testing.T) {
	got := strings.Join(outcomes(t, false, true), " ")
	want := "ServerError(EOF) ServerError(unexpected EOF) io.ErrUnexpectedEOF ok"
	if got != want {
		t.Errorf("outcomes of a cut request:\n got %s\nwant %s", got, want)
	}
}

// A connection reset (the peer closes with SO_LINGER 0) while a call is pending: the call fails
// with the read's error, a *net.OpError holding ECONNRESET, and every later call too.
func TestReset(t *testing.T) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	go func() {
		a, err := l.Accept()
		if err != nil {
			return
		}
		buf := make([]byte, 64)
		a.Read(buf) // the request's first bytes
		a.(*net.TCPConn).SetLinger(0)
		a.Close()
	}()
	c, err := rpc.Dial("tcp", l.Addr().String())
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	var r difftest.Reply
	err = c.Call("Arith.Add", &difftest.Args{}, &r)
	var oe *net.OpError
	if !errors.As(err, &oe) || !errors.Is(err, syscall.ECONNRESET) || oe.Op != "read" {
		t.Fatalf("call during a reset: %#v (%v)", err, err)
	}
	err2 := c.Call("Arith.Add", &difftest.Args{}, &r)
	if err2 == nil {
		t.Fatal("a call after the reset succeeded")
	}
	if !reflect.DeepEqual(err2, err) && err2 != rpc.ErrShutdown {
		t.Fatalf("a call after the reset: %v (want the reset's error or ErrShutdown)", err2)
	}
}

// The server closes the connection while a call runs (its process gone): the pending call fails
// with an unexpected end of stream (an end of stream at a message boundary, not after Close).
func TestServerClosesMidCall(t *testing.T) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	go func() {
		a, err := l.Accept()
		if err != nil {
			return
		}
		drain(a)
		a.Close()
	}()
	c, err := rpc.Dial("tcp", l.Addr().String())
	if err != nil {
		t.Fatal(err)
	}
	var r difftest.Reply
	if err := c.Call("Arith.Add", &difftest.Args{}, &r); err != io.ErrUnexpectedEOF {
		t.Fatalf("call when the server closes: %v", err)
	}
	if err := c.Call("Arith.Add", &difftest.Args{}, &r); err != rpc.ErrShutdown {
		t.Fatalf("call after the server closed: %v", err)
	}
	if err := c.Close(); err != nil {
		t.Fatalf("Close after the server closed: %v", err)
	}
}

// drain reads what the peer sends until it pauses (so that a Close sends FIN, not RST).
func drain(c net.Conn) {
	buf := make([]byte, 4096)
	for {
		c.SetReadDeadline(time.Now().Add(200 * time.Millisecond))
		if _, err := c.Read(buf); err != nil {
			return
		}
	}
}
