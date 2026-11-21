package rpcdifftest_test

import (
	"bufio"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"net/rpc"
	"os"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	difftest "models.lab/internal/rpcdifftest"
	"models.lab/internal/rpcdifftest/codec"
)

// One server for the package (the DefaultServer and the DefaultServeMux).
var (
	arith *difftest.Arith
	addr  string
	ids   atomic.Uint64 // fresh call ids (Wait/Signal gates, Count's runs), across -count runs
)

// fresh returns n fresh ids, the first of them.
func fresh(n uint64) uint64 {
	return ids.Add(n) - n + 1
}

func TestMain(m *testing.M) {
	codec.Register()
	arith = difftest.NewArith()
	if err := rpc.RegisterName("Arith", arith); err != nil {
		panic(err)
	}
	rpc.HandleHTTP()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		panic(err)
	}
	addr = l.Addr().String()
	l.Close()
	go http.ListenAndServe(addr, nil)
	for i := 0; ; i++ {
		c, err := net.Dial("tcp", addr)
		if err == nil {
			c.Close()
			break
		}
		if i > 200 {
			panic("server did not start")
		}
		time.Sleep(10 * time.Millisecond)
	}
	os.Exit(m.Run())
}

func dial(t *testing.T) *rpc.Client {
	c, err := rpc.DialHTTP("tcp", addr)
	if err != nil {
		t.Fatal(err)
	}
	return c
}

func TestCalls(t *testing.T) {
	c := dial(t)
	defer c.Close()
	var r difftest.Reply
	if err := c.Call("Arith.Add", &difftest.Args{A: 2, B: 3}, &r); err != nil || r.C != 5 {
		t.Fatalf("Add: %v %v", r, err)
	}
	var r2 difftest.Reply
	if err := c.Call("Arith.Add", difftest.Args{A: 1, B: 1}, &r2); err != nil || r2.C != 2 {
		t.Fatalf("Add (value args): %v %v", r2, err)
	}
	var s string
	if err := c.Call("Arith.Echo", "hello", &s); err != nil || s != "hello" {
		t.Fatalf("Echo: %q %v", s, err)
	}
	var e string
	if err := c.Call("Arith.Echo", "", &e); err != nil || e != "" {
		t.Fatalf("Echo empty: %q %v", e, err)
	}
	var tg difftest.Tags
	if err := c.Call("Arith.Keys", &difftest.Tags{"a": 1, "b": 2}, &tg); err != nil ||
		len(tg) != 2 || tg["a!"] != 2 || tg["b!"] != 3 {
		t.Fatalf("Keys: %v %v", tg, err)
	}
	var te difftest.Tags
	if err := c.Call("Arith.Keys", &difftest.Tags{}, &te); err != nil || te == nil || len(te) != 0 {
		t.Fatalf("Keys empty: %#v %v", te, err)
	}
}

// A method's error is a ServerError with its message, and the reply is not decoded.
func TestServerError(t *testing.T) {
	c := dial(t)
	defer c.Close()
	var r difftest.Reply
	err := c.Call("Arith.Fail", &difftest.Args{}, &r)
	if se, ok := err.(rpc.ServerError); !ok || string(se) != "arith: fail" || r.C != 0 {
		t.Fatalf("Fail: %#v %v", err, r)
	}
	// the client still works
	if err := c.Call("Arith.Add", &difftest.Args{A: 1}, &r); err != nil || r.C != 1 {
		t.Fatalf("Add after Fail: %v %v", r, err)
	}
}

func TestLookupErrors(t *testing.T) {
	c := dial(t)
	defer c.Close()
	var r difftest.Reply
	cases := map[string]string{
		"Arith.Nope": "rpc: can't find method Arith.Nope",
		"Nope.Add":   "rpc: can't find service Nope.Add",
		"NoDot":      "rpc: service/method request ill-formed: NoDot",
	}
	for sm, want := range cases {
		err := c.Call(sm, &difftest.Args{}, &r)
		if se, ok := err.(rpc.ServerError); !ok || string(se) != want {
			t.Errorf("%s: %#v, want ServerError %q", sm, err, want)
		}
	}
	if err := c.Call("Arith.Add", &difftest.Args{A: 4}, &r); err != nil || r.C != 4 {
		t.Fatalf("Add after lookup errors: %v %v", r, err)
	}
}

// Arguments of a type the method does not take (gob refuses string into a struct): a
// ServerError, and the connection still works. A reply of a type the caller's reply value does
// not take: an error, and the client is shut down (Go's reader stops at a body it cannot decode).
//
// Real only: the model panics on decoding a value of one type into another (outside its subset,
// models/net/rpc/rpcgen_core.py's documented deviations).
func TestArgTypeMismatch(t *testing.T) {
	if model {
		t.Skip("decoding across types is outside the model (it panics)")
	}
	c := dial(t)
	defer c.Close()
	var r difftest.Reply
	err := c.Call("Arith.Add", "str", &r)
	if _, ok := err.(rpc.ServerError); !ok {
		t.Fatalf("Add(string): %#v", err)
	}
	if err := c.Call("Arith.Add", &difftest.Args{A: 6}, &r); err != nil || r.C != 6 {
		t.Fatalf("Add after a mismatch: %v %v", r, err)
	}
	var s string
	err = c.Call("Arith.Add", &difftest.Args{A: 1}, &s)
	if err == nil || !strings.HasPrefix(err.Error(), "reading body ") {
		t.Fatalf("Add into a string reply: %v", err)
	}
	// The stream is out of step after the failed body: the next call fails, either with
	// ErrShutdown (the reader already stopped) or with the reader's error (the call was sent
	// before the reader stopped). Both happen, in real net/rpc and in the model.
	var r2 difftest.Reply
	if err := c.Call("Arith.Add", &difftest.Args{A: 6}, &r2); err == nil {
		t.Fatalf("Add after a reply mismatch: %v %v", r2, err)
	}
}

// Calls on one client run concurrently at the server: Wait(id) returns only after Signal(id),
// sent later on the same client.
func TestConcurrentCalls(t *testing.T) {
	c := dial(t)
	defer c.Close()
	var wg sync.WaitGroup
	errs := make(chan error, 40)
	b := fresh(20)
	for i := b; i < b+20; i++ {
		wg.Add(1)
		go func(id uint64) {
			defer wg.Done()
			var r difftest.Reply
			if err := c.Call("Arith.Wait", &difftest.Args{A: id}, &r); err != nil || r.C != id {
				errs <- fmt.Errorf("Wait(%d): %v %v", id, r, err)
			}
		}(i)
	}
	time.Sleep(50 * time.Millisecond)
	for i := b; i < b+20; i++ {
		var r difftest.Reply
		if err := c.Call("Arith.Signal", &difftest.Args{A: i}, &r); err != nil {
			t.Fatalf("Signal(%d): %v", i, err)
		}
	}
	wg.Wait()
	close(errs)
	for err := range errs {
		t.Error(err)
	}
}

func TestClose(t *testing.T) {
	c := dial(t)
	if err := c.Close(); err != nil {
		t.Fatalf("Close: %v", err)
	}
	var r difftest.Reply
	if err := c.Call("Arith.Add", &difftest.Args{}, &r); err != rpc.ErrShutdown {
		t.Fatalf("Call after Close: %v", err)
	}
	if err := c.Close(); err != rpc.ErrShutdown {
		t.Fatalf("second Close: %v", err)
	}
}

// A proxy whose connections the test can cut.
type proxy struct {
	addr  string
	mu    sync.Mutex
	conns []net.Conn
}

func newProxy(t *testing.T) *proxy {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	p := &proxy{addr: l.Addr().String()}
	go func() {
		for {
			a, err := l.Accept()
			if err != nil {
				return
			}
			b, err := net.Dial("tcp", addr)
			if err != nil {
				a.Close()
				continue
			}
			p.mu.Lock()
			p.conns = append(p.conns, a, b)
			p.mu.Unlock()
			go io.Copy(a, b)
			go io.Copy(b, a)
		}
	}()
	t.Cleanup(func() { l.Close(); p.cut() })
	return p
}

func (p *proxy) cut() {
	p.mu.Lock()
	defer p.mu.Unlock()
	for _, c := range p.conns {
		c.Close()
	}
	p.conns = nil
}

// A broken connection fails the pending calls and every later one.
func TestBrokenConnection(t *testing.T) {
	p := newProxy(t)
	c, err := rpc.DialHTTP("tcp", p.addr)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	done := make(chan error, 1)
	w := fresh(1)
	go func() {
		var r difftest.Reply
		done <- c.Call("Arith.Wait", &difftest.Args{A: w}, &r)
	}()
	time.Sleep(50 * time.Millisecond)
	p.cut()
	select {
	case err := <-done:
		if err == nil {
			t.Fatal("pending call succeeded after the cut")
		}
	case <-time.After(5 * time.Second):
		t.Fatal("pending call did not fail after the cut")
	}
	var r difftest.Reply
	if err := c.Call("Arith.Add", &difftest.Args{}, &r); err == nil {
		t.Fatal("call after the cut succeeded")
	}
	arith.Signal(&difftest.Args{A: w}, &difftest.Reply{})
}

// At most once: calls through a proxy cut at random times; a call that returned nil ran exactly
// once, any other call at most once.
func TestAtMostOnce(t *testing.T) {
	base := fresh(1 << 20)
	ok := map[uint64]bool{}
	var mu sync.Mutex
	id := base
	for round := 0; round < 20; round++ {
		p := newProxy(t)
		c, err := rpc.DialHTTP("tcp", p.addr)
		if err != nil {
			t.Fatal(err)
		}
		var wg sync.WaitGroup
		for g := 0; g < 4; g++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				for k := 0; k < 25; k++ {
					mu.Lock()
					id++
					my := id
					mu.Unlock()
					var r difftest.Reply
					if err := c.Call("Arith.Count", &difftest.Args{A: my}, &r); err == nil {
						if r.C != my {
							t.Errorf("Count(%d) replied %d", my, r.C)
						}
						mu.Lock()
						ok[my] = true
						mu.Unlock()
					}
				}
			}()
		}
		time.Sleep(time.Duration(round%5) * time.Millisecond)
		p.cut()
		wg.Wait()
		c.Close()
	}
	time.Sleep(100 * time.Millisecond)
	for i := base + 1; i <= id; i++ {
		n := arith.Runs(i)
		if n > 1 || (ok[i] && n != 1) {
			t.Errorf("call %d: ran %d times, returned ok %v", i, n, ok[i])
		}
	}
}

func TestDialErrors(t *testing.T) {
	if _, err := rpc.DialHTTPPath("tcp", addr, "/nope"); err == nil {
		t.Error("DialHTTPPath to an unregistered path succeeded")
	}
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	dead := l.Addr().String()
	go func() {
		for {
			c, err := l.Accept()
			if err != nil {
				return
			}
			c.Write([]byte("garbage\n\n"))
			c.Close()
		}
	}()
	if _, err := rpc.DialHTTP("tcp", dead); err == nil {
		t.Error("DialHTTP to a non-RPC server succeeded")
	}
	l.Close()
	if _, err := rpc.DialHTTP("tcp", dead); err == nil {
		t.Error("DialHTTP to a closed port succeeded")
	}
}

// A request that is not CONNECT gets 405; the mux 404s an unknown path.
func TestHTTPStatus(t *testing.T) {
	for req, want := range map[string]string{
		"GET /_goRPC_ HTTP/1.0\r\n\r\n":  " 405 ",
		"CONNECT /nope HTTP/1.0\r\n\r\n": " 404 ",
		"GET /_goRPC_ HTTP/1.0\n\n":      " 405 ",
	} {
		c, err := net.Dial("tcp", addr)
		if err != nil {
			t.Fatal(err)
		}
		c.Write([]byte(req))
		line, _ := bufio.NewReader(c).ReadString('\n')
		c.Close()
		if !strings.HasPrefix(line, "HTTP/1.") || !strings.Contains(line, want) {
			t.Errorf("%q: status line %q, want %q", req, line, want)
		}
	}
}

func TestRegisterErrors(t *testing.T) {
	if err := rpc.RegisterName("Arith", difftest.NewArith()); err == nil {
		t.Error("RegisterName of a taken name succeeded")
	}
	if err := rpc.RegisterName("", difftest.NewArith()); err == nil {
		t.Error("RegisterName with no name succeeded")
	}
	quiet() // real net/rpc logs the next error
	if err := rpc.RegisterName("NoMethods", &difftest.NoMethods{}); err == nil {
		t.Error("RegisterName of a receiver with no suitable methods succeeded")
	}
	s := rpc.NewServer()
	if err := s.RegisterName("NoMethods", &difftest.NoMethods{}); err == nil {
		t.Error("RegisterName (new server) of a receiver with no suitable methods succeeded")
	}
	if err := s.RegisterName("", difftest.NewArith()); err == nil {
		t.Error("RegisterName (new server) with no name succeeded")
	}
	if err := s.RegisterName("Arith", difftest.NewArith()); err != nil {
		t.Errorf("RegisterName on a new server: %v", err)
	}
	if err := s.RegisterName("Arith", difftest.NewArith()); err == nil {
		t.Error("RegisterName of a name taken on a new server succeeded")
	}
	func() {
		defer func() {
			if recover() == nil {
				t.Error("a second HandleHTTP did not panic")
			}
		}()
		rpc.HandleHTTP()
	}()
	// a second server on fresh paths (fresh across -count runs): the first HandleHTTP
	// registers, a second on the same rpc path panics
	id := fresh(1)
	p, dp := fmt.Sprintf("/difftest_rpc_%d", id), fmt.Sprintf("/difftest_debug_%d", id)
	s.HandleHTTP(p, dp)
	func() {
		defer func() {
			if recover() == nil {
				t.Error("a second HandleHTTP on the same paths did not panic")
			}
		}()
		s.HandleHTTP(p, dp)
	}()
}

// The integer types the codec carries besides uint64 (int, int32, uint8).
func TestNums(t *testing.T) {
	c := dial(t)
	defer c.Close()
	var r difftest.Nums
	if err := c.Call("Arith.Neg", &difftest.Nums{I: -5, J: 7, K: 3}, &r); err != nil ||
		r != (difftest.Nums{I: 5, J: -7, K: 252}) {
		t.Fatalf("Neg: %v %v", r, err)
	}
}

var registerGreeter sync.Once

// Register publishes a receiver under its type's name; a second Register of the type fails.
// http.Serve serves the DefaultServeMux (rpc's handler) on a listener of the caller's.
func TestRegisterServe(t *testing.T) {
	registerGreeter.Do(func() { // once per process (the DefaultServer keeps it across -count runs)
		if err := rpc.Register(&difftest.Greeter{}); err != nil {
			t.Fatalf("Register: %v", err)
		}
	})
	if err := rpc.Register(&difftest.Greeter{}); err == nil {
		t.Error("a second Register of the type succeeded")
	}
	s := rpc.NewServer()
	if err := s.Register(&difftest.Greeter{}); err != nil {
		t.Errorf("Register on a new server: %v", err)
	}
	quiet()
	if err := s.Register(&difftest.NoMethods{}); err == nil {
		t.Error("Register of a receiver with no suitable methods succeeded")
	}
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer l.Close()
	go http.Serve(l, nil)
	c, err := rpc.DialHTTP("tcp", l.Addr().String())
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	var r string
	if err := c.Call("Greeter.Hello", "you", &r); err != nil || r != "hello you" {
		t.Fatalf("Greeter.Hello: %q %v", r, err)
	}
	var a difftest.Reply
	if err := c.Call("Arith.Add", &difftest.Args{A: 4, B: 5}, &a); err != nil || a.C != 9 {
		t.Fatalf("Arith.Add through Serve: %v %v", a, err)
	}
}

// The CONNECT handshake by hand: ReadResponse on a fresh bufio.Reader over the connection, then NewClient over the
// connection itself.
func TestNewClientAfterConnect(t *testing.T) {
	conn, err := net.Dial("tcp", addr)
	if err != nil {
		t.Fatal(err)
	}
	io.WriteString(conn, "CONNECT "+rpc.DefaultRPCPath+" HTTP/1.0\n\n")
	resp, err := http.ReadResponse(bufio.NewReader(conn), &http.Request{Method: "CONNECT"})
	if err != nil || resp == nil || resp.Status != "200 Connected to Go RPC" || resp.StatusCode != 200 ||
		resp.Proto != "HTTP/1.0" {
		t.Fatalf("ReadResponse: %+v %v", resp, err)
	}
	c := rpc.NewClient(conn)
	defer c.Close()
	var r difftest.Reply
	if err := c.Call("Arith.Add", &difftest.Args{A: 4, B: 5}, &r); err != nil || r.C != 9 {
		t.Fatalf("Add: %v %v", r, err)
	}
}

// ReadResponse on responses other than net/rpc's: a 404 with a header and a body, and malformed
// status lines.
func TestReadResponse(t *testing.T) {
	for _, tc := range []struct {
		in     string
		status string
		code   int
	}{
		{"HTTP/1.0 404 Not Found\r\nContent-Type: text/plain\r\n\r\nbody", "404 Not Found", 404},
		{"HTTP/1.1 200 OK\n\n", "200 OK", 200},
		{"HTTP/1.0 2x0 OK\n\n", "", -1},
		{"HTTP/1.0\n\n", "", -1},
		{"HTTP/1.0 200", "", -1},
	} {
		resp, err := http.ReadResponse(bufio.NewReader(strings.NewReader(tc.in)), &http.Request{Method: "GET"})
		if tc.code < 0 {
			if err == nil {
				t.Errorf("%q: no error", tc.in)
			}
			continue
		}
		if err != nil || resp.Status != tc.status || resp.StatusCode != tc.code {
			t.Errorf("%q: %+v %v", tc.in, resp, err)
		}
	}
}

// quiet discards log's output (both net/rpcs log Register's errors; not with io.Discard: log
// then skips formatting).
func quiet() { log.SetOutput(sink{}) }

type sink struct{}

func (sink) Write(p []byte) (int, error) { return len(p), nil }
