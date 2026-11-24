// Package httpdriver is the executable specification of what our proofs rely on from Go's
// net/http server (as etcd's peer handlers and the dsverify kits' net/rpc over HTTP use it), as a
// deployable server and client: each section below names one behavior the library guarantees,
// exercises it, and panics if it fails. Its top-level robustness theorem says the client never
// panics, in every execution over the net extension (cut, reset or delayed connections, refused
// dials), so each section asserts only what holds whatever the network does: properties of the
// responses the client received in full, nothing of a request whose response did not arrive.
//
// Two machines, each a process: the server (Server) serves a ServeMux at Addr; the client
// (Client) opens random connections from random goroutines and sends on each a random number of
// HTTP/1.1 requests, written on the connection, and reads each response with http.ReadResponse.
// (Not with an http.Client: net/http's Transport is outside the model of net/http, models/net/http,
// which this driver runs over; notes/library-drivers.md.) Every choice is the program's
// nondeterminism (primitive.RandomUint64): the theorem covers all of them.
package httpdriver

import (
	"bufio"
	"io"
	"net"
	"net/http"
	"strconv"
	"sync"

	"github.com/goose-lang/primitive"
)

// Addr is the server's address.
const Addr = "127.0.0.1:7401"

// Bounds on the client's random choices.
const (
	maxConns = 4  // connections, each from its own goroutine
	maxReqs  = 4  // requests per connection
	maxLen   = 32 // length of a body or a header value
)

// The status the /status handler answers with.
const teapot = 418

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

// echo answers the request's method, path and X-Driver header in headers, and its body as the
// response's body; 500 if the body could not be read in full.
func echo(w http.ResponseWriter, r *http.Request) {
	body, err := io.ReadAll(r.Body)
	if err != nil {
		w.WriteHeader(http.StatusInternalServerError)
		return
	}
	w.Header().Set("X-Method", r.Method)
	w.Header().Set("X-Path", r.URL.Path)
	w.Header().Set("X-Echo", r.Header.Get("X-Driver"))
	w.WriteHeader(http.StatusOK)
	w.Write(body)
}

// teapotHandler answers with the status teapot and a fixed body.
func teapotHandler(w http.ResponseWriter, r *http.Request) {
	w.WriteHeader(teapot)
	w.Write([]byte("short and stout"))
}

// Server serves the mux at Addr. It returns only if it cannot listen, or when Serve returns.
func Server() {
	mux := http.NewServeMux()
	mux.HandleFunc("/echo", echo)
	mux.HandleFunc("/status", teapotHandler)
	l, err := net.Listen("tcp", Addr)
	if err != nil {
		return
	}
	http.Serve(l, mux)
}

// ---------------------------------------------------------------------------------------------
// The client.

// randomWord is a random string of letters of length at most maxLen.
func randomWord() string {
	n := below(maxLen + 1)
	b := make([]byte, n)
	for i := range b {
		b[i] = byte('a' + below(26))
	}
	return string(b)
}

// request is a request the client sends, and what it checks of the response.
type request struct {
	raw   string // the request's bytes on the connection
	kind  string // "echo", "status", "notfound" or "bad"
	meth  string
	value string // the X-Driver header's value
	body  string
}

// randomRequest is a request of a random kind.
func randomRequest() request {
	switch below(4) {
	case 0:
		meth := "POST"
		if below(2) == 0 {
			meth = "PUT"
		}
		v, b := randomWord(), randomWord()
		raw := meth + " /echo HTTP/1.1\r\nHost: driver\r\nX-Driver: " + v + "\r\nContent-Length: " +
			strconv.Itoa(len(b)) + "\r\n\r\n" + b
		return request{raw: raw, kind: "echo", meth: meth, value: v, body: b}
	case 1:
		return request{raw: "GET /status HTTP/1.1\r\nHost: driver\r\n\r\n", kind: "status"}
	case 2:
		return request{raw: "GET /nope/" + randomWord() + " HTTP/1.1\r\nHost: driver\r\n\r\n", kind: "notfound"}
	default:
		return request{raw: "NOT A REQUEST\r\n\r\n", kind: "bad"}
	}
}

// check is what the client relies on from a response received in full (its head parsed, its
// body read to the end). The network may cut the client-to-server direction alone, so the server
// may have read only a prefix of the request: its own 400 is then a possible answer to any request.
func check(q request, resp *http.Response, body string) {
	switch q.kind {
	case "echo":
		// Section echo: a handler sees the request as the client sent it: its method, path,
		// header values and body (a 200 is the handler's own answer: it read the whole body).
		if resp.StatusCode == http.StatusOK {
			if resp.Header.Get("X-Method") != q.meth || resp.Header.Get("X-Path") != "/echo" ||
				resp.Header.Get("X-Echo") != q.value || body != q.body {
				panic("echo: the handler did not see the request as sent")
			}
			reached("echo")
		}
	case "status":
		// Section status: the client receives the status and body the handler wrote -- or the
		// server's own 400, if the network cut the request short (the server then answers what it
		// read, and the handler never ran).
		if resp.StatusCode == teapot {
			if body != "short and stout" {
				panic("status: the handler's status with another body")
			}
			reached("status")
		} else if resp.StatusCode != http.StatusBadRequest {
			panic("status: neither the handler's status nor the server's own 400")
		}
	case "notfound":
		// Section mux: a path no pattern of the ServeMux matches is answered 404 (or the server's
		// own 400, for a request the network cut short); never by a handler.
		if resp.StatusCode == http.StatusNotFound {
			reached("mux")
		} else if resp.StatusCode != http.StatusBadRequest {
			panic("mux: an unmatched path was answered by neither 404 nor the server's own 400")
		}
	default:
		// Section bad-request: a request that does not parse is answered 400 by the server
		// itself, and the connection is closed after it.
		if resp.StatusCode != http.StatusBadRequest {
			panic("bad-request: a malformed request was not answered 400")
		}
		reached("bad-request")
	}
}

// session sends random requests on one connection, one at a time, and checks each response.
func session() {
	c, err := net.Dial("tcp", Addr)
	if err != nil {
		return
	}
	br := bufio.NewReader(c)
	n := 1 + below(maxReqs)
	for i := uint64(0); i < n; i++ {
		q := randomRequest()
		if _, err := c.Write([]byte(q.raw)); err != nil {
			break
		}
		// Section keep-alive: on one connection, the responses come in the order of the
		// requests (each response checked against its own request).
		resp, err := http.ReadResponse(br, nil)
		if err != nil {
			break
		}
		b, err := io.ReadAll(resp.Body)
		if err != nil {
			break
		}
		check(q, resp, string(b))
		reached("keep-alive")
		if q.kind == "bad" {
			break // the server closes the connection after a 400
		}
	}
	c.Close()
}

// Client runs random sessions from random goroutines.
func Client() {
	// Section concurrent-connections: connections served concurrently each meet their own
	// sections' properties.
	var wg sync.WaitGroup
	conns := 1 + below(maxConns)
	for k := uint64(0); k < conns; k++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			session()
		}()
	}
	wg.Wait()
	reached("concurrent-connections")
}
