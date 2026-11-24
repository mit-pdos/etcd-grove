// Package rpcdriver is the executable specification of what our proofs rely on from Go's net/rpc
// (the library etcd-grove's dsverify kits use: SwiftPaxos, EPaxos, CRAQ, Gryff), as a deployable
// server and client: each section below names one behavior the library guarantees, exercises it,
// and panics if it fails. Its top-level robustness theorem says the client never panics, in every
// execution over the net extension (cut, reset or delayed connections, refused dials), so each
// section asserts only what holds whatever the network does: properties of calls that succeeded,
// and the shape of the errors otherwise.
//
// Two machines, each a process: the server (Server) serves one service over raw TCP (rpc.Accept at
// TCPAddr) and over HTTP (rpc.HandleHTTP and http.Serve at HTTPAddr, as the kits do); the client
// (Client) dials either way, at random, and makes calls of random kinds, sizes and concurrency.
// Every choice is the program's nondeterminism (primitive.RandomUint64): the theorem covers all of
// them. The behaviors and the call sites relying on them: notes/library-drivers.md.
package rpcdriver

import (
	"net"
	"net/http"
	"net/rpc"
	"sync"

	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/net/rpcdriver/service"
)

// TCPAddr is where the server serves net/rpc over raw TCP; HTTPAddr where it serves it over HTTP.
const (
	TCPAddr  = "127.0.0.1:7211"
	HTTPAddr = "127.0.0.1:7212"
)

// Bounds on the client's random choices.
const (
	maxConns   = 4  // connections the client dials
	maxCalls   = 8  // calls per connection
	maxWorkers = 4  // goroutines calling concurrently on one connection
	maxData    = 64 // bytes of a request's payload
)

// reached marks a section's check as reached; it does nothing (the tests count with it, to show
// that every section's property is checked on a real run: non-vacuity).
var reached = func(section string) {}

// below is a random number in [0, n) (0 if n is 0).
func below(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	return primitive.RandomUint64() % n
}

// ---------------------------------------------------------------------------------------------
// The server.

// Server (after the program's Register of the codec) registers the service, then serves it over raw TCP and over HTTP. It returns only if it
// cannot listen.
func Server() {
	// Section register: registering a receiver of an exported type with a suitable method
	// succeeds; registering one with no suitable method fails.
	svc := service.New()
	if err := rpc.Register(svc); err != nil {
		panic("register: a valid receiver was refused")
	}
	if err := rpc.Register(&service.NoMethods{}); err == nil {
		panic("register: a receiver with no methods was accepted")
	}
	reached("register")

	// Serving over HTTP: rpc.HandleHTTP registers the RPC path on http.DefaultServeMux.
	rpc.HandleHTTP()
	hl, err := net.Listen("tcp", HTTPAddr)
	if err != nil {
		return
	}
	go http.Serve(hl, nil)

	// Serving over raw TCP.
	tl, err := net.Listen("tcp", TCPAddr)
	if err != nil {
		return
	}
	rpc.Accept(tl)
}

// ---------------------------------------------------------------------------------------------
// The client.

// failMsgs are the errors a request may ask the method to answer with.
var failMsgs = []string{"no such key", "not leader", "x"}

// dial connects to the server, over raw TCP or over HTTP at random.
func dial() (*rpc.Client, error) {
	if below(2) == 0 {
		return rpc.Dial("tcp", TCPAddr)
	}
	return rpc.DialHTTP("tcp", HTTPAddr)
}

// counter hands out the ids of the client's requests, unique within the client's run (from a
// random start, so that the runs of a test against one server rarely share ids).
type counter struct {
	mu   sync.Mutex
	next uint64
}

func (c *counter) take() uint64 {
	c.mu.Lock()
	id := c.next
	c.next = id + 1
	c.mu.Unlock()
	return id
}

// randomArgs is a request with a fresh id, a random payload and, at random, an error to answer
// with.
func randomArgs(ids *counter) *service.Args {
	data := make([]byte, below(maxData+1))
	for i := range data {
		data[i] = byte(primitive.RandomUint64())
	}
	fail := ""
	if below(2) == 0 {
		fail = failMsgs[below(uint64(len(failMsgs)))]
	}
	return &service.Args{ID: ids.take(), Data: data, Fail: fail}
}

// check is what the client relies on from one call's outcome, given its request.
func check(a *service.Args, r *service.Reply, err error) {
	if err == nil {
		// Section call-success: a call that returns nil ran the method exactly once, on these
		// arguments, and its reply is the method's.
		if a.Fail != "" {
			panic("call-success: a call whose method failed returned nil")
		}
		if r.ID != a.ID || string(r.Data) != string(a.Data) {
			panic("call-success: the reply is not the method's answer to this request")
		}
		if r.Runs != 1 {
			panic("call-success: the method ran more than once on this request")
		}
		reached("call-success")
		return
	}
	// Section server-error: a rpc.ServerError is the method's own error, after it ran on this
	// request: its message is the one the method answered with.
	if se, ok := err.(rpc.ServerError); ok {
		if a.Fail == "" || string(se) != a.Fail {
			panic("server-error: a ServerError that is not the method's answer")
		}
		reached("server-error")
		return
	}
	// Section other-errors: any other error (the connection's, io.EOF, rpc.ErrShutdown) says
	// nothing about whether the method ran, and the reply is not looked at.
	reached("other-error")
}

// callOn makes calls on the connection c, from random workers, with Call or Go at random.
func callOn(c *rpc.Client, ids *counter) {
	var wg sync.WaitGroup
	workers := 1 + below(maxWorkers)
	for w := uint64(0); w < workers; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			// Section concurrent-calls: calls made concurrently on one client each get their
			// own outcome (each reply is checked against its own request).
			calls := below(maxCalls + 1)
			for i := uint64(0); i < calls; i++ {
				a := randomArgs(ids)
				r := &service.Reply{}
				var err error
				if below(2) == 0 {
					err = c.Call("Svc.Echo", a, r)
				} else {
					call := c.Go("Svc.Echo", a, r, make(chan *rpc.Call, 1))
					<-call.Done
					err = call.Error
				}
				check(a, r, err)
				reached("concurrent-calls")
			}
		}()
	}
	wg.Wait()
}

// Client (after the program's Register of the codec) dials the server a random number of times, makes random calls on each connection and
// checks every outcome, then closes the connection.
func Client() {
	ids := &counter{next: primitive.RandomUint64()}
	conns := 1 + below(maxConns)
	for k := uint64(0); k < conns; k++ {
		c, err := dial()
		if err != nil {
			// Section dial: a dial may fail (no server yet, a refused or cut connection).
			continue
		}
		callOn(c, ids)

		// Section close: after Close, a call fails with an error that is not a ServerError.
		c.Close()
		a := randomArgs(ids)
		if err := c.Call("Svc.Echo", a, &service.Reply{}); err == nil {
			panic("close: a call on a closed client succeeded")
		} else if _, ok := err.(rpc.ServerError); ok {
			panic("close: a call on a closed client got a ServerError")
		}
		reached("close")
	}
}
