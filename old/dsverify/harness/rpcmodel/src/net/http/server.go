// Package http is the dsverify lab's model of the part of Go's net/http (Go 1.27.3) that net/rpc
// over HTTP uses (notes/craq-net.md decision 1): ListenAndServe and Serve with a handler or
// the DefaultServeMux, Handle, a ResponseWriter that can be hijacked. Goose translates it in place of
// the real package (harness/rpcmodel/goroot.sh); the harness proves its specs once over the net
// model.
//
// A connection carries one request head (up to a blank line; "\n" or "\r\n" line ends), whose
// request line is "METHOD URI PROTO". The mux matches the URI exactly (the model's patterns are
// paths without wildcards, as net/rpc's). A handler that does not hijack the connection gets it
// closed after it returns (Go would keep it alive for another request; no client of the model
// sends one). Errors from Accept are retried (Go retries temporary ones and returns on others,
// Serve after closing its listener: the model's retry also covers a listener that never accepts
// again).
package http

import (
	"errors"
	"net"
	"sync"
)

// Handler responds to an HTTP request.
type Handler interface {
	ServeHTTP(ResponseWriter, *Request)
}

// ResponseWriter is the part of Go's ResponseWriter the model's handlers use.
type ResponseWriter interface {
	Write([]byte) (int, error)
	WriteHeader(statusCode int)
}

// Hijacker lets a handler take over the connection. Go's returns a bufio.ReadWriter as well; the
// model's handlers (net/rpc's ServeHTTP) read and write the connection directly.
type Hijacker interface {
	Hijack() (net.Conn, error)
}

// Request is the part of Go's Request the model's handlers use.
type Request struct {
	Method     string
	RequestURI string
}

// ServeMux is an HTTP request multiplexer: exact paths to handlers.
type ServeMux struct {
	mu sync.Mutex
	m  map[string]Handler
}

// NewServeMux allocates and returns a new ServeMux.
func NewServeMux() *ServeMux {
	return &ServeMux{m: make(map[string]Handler)}
}

// DefaultServeMux is the default ServeMux used by Serve.
var DefaultServeMux = NewServeMux()

// Handle registers the handler for the given pattern; it panics if the pattern is taken (as Go).
func (mux *ServeMux) Handle(pattern string, handler Handler) {
	if pattern == "" {
		panic("http: invalid pattern")
	}
	if handler == nil {
		panic("http: nil handler")
	}
	mux.mu.Lock()
	_, dup := mux.m[pattern]
	if dup {
		mux.mu.Unlock()
		panic("http: multiple registrations for " + pattern)
	}
	mux.m[pattern] = handler
	mux.mu.Unlock()
}

// Handle registers the handler for the given pattern in the DefaultServeMux.
func Handle(pattern string, handler Handler) {
	DefaultServeMux.Handle(pattern, handler)
}

// ServeHTTP dispatches the request to the handler registered for its URI, or answers 404.
func (mux *ServeMux) ServeHTTP(w ResponseWriter, r *Request) {
	mux.mu.Lock()
	h, ok := mux.m[r.RequestURI]
	mux.mu.Unlock()
	if !ok {
		w.WriteHeader(404)
		w.Write([]byte("404 page not found\n"))
		return
	}
	h.ServeHTTP(w, r)
}

// ListenAndServe listens on the TCP network address addr and serves each connection in its own
// goroutine with handler (nil: the DefaultServeMux). It returns only if the listen fails.
func ListenAndServe(addr string, handler Handler) error {
	l, err := net.Listen("tcp", addr)
	if err != nil {
		return err
	}
	for {
		c, err2 := l.Accept()
		if err2 != nil {
			continue
		}
		go serveConn(c, handler)
	}
}

// Serve accepts connections on l and serves each in its own goroutine with handler (nil: the
// DefaultServeMux), as ListenAndServe after its Listen. It never returns: Accept errors are
// retried, as in ListenAndServe (Go returns on an error that is not temporary, after closing l).
func Serve(l net.Listener, handler Handler) error {
	for {
		c, err := l.Accept()
		if err != nil {
			continue
		}
		go serveConn(c, handler)
	}
}

var errHead = errors.New("http: malformed request head")

// maxHead bounds a request head.
const maxHead uint64 = 4096

// readHead reads a request head, up to and including its blank line.
func readHead(c net.Conn) ([]byte, error) {
	head := make([]byte, 0, 64)
	buf := make([]byte, 1)
	for {
		if uint64(len(head)) >= maxHead {
			return nil, errHead
		}
		_, err := c.Read(buf)
		if err != nil {
			return nil, err
		}
		head = append(head, buf[0])
		n := len(head)
		if n >= 2 && head[n-1] == '\n' && head[n-2] == '\n' {
			return head, nil
		}
		if n >= 3 && head[n-1] == '\n' && head[n-2] == '\r' && head[n-3] == '\n' {
			return head, nil
		}
	}
}

// parseRequestLine splits the head's first line "METHOD URI PROTO".
func parseRequestLine(head []byte) (string, string, bool) {
	end := 0
	for end < len(head) && head[end] != '\n' {
		end = end + 1
	}
	line := head[:end]
	if len(line) > 0 && line[len(line)-1] == '\r' {
		line = line[:len(line)-1]
	}
	sp1 := -1
	sp2 := -1
	for i := 0; i < len(line); i++ {
		if line[i] == ' ' {
			if sp1 < 0 {
				sp1 = i
			} else if sp2 < 0 {
				sp2 = i
			}
		}
	}
	if sp1 <= 0 || sp2 <= sp1+1 || sp2 == len(line)-1 {
		return "", "", false
	}
	return string(line[:sp1]), string(line[sp1+1 : sp2]), true
}

type response struct {
	conn        net.Conn
	wroteHeader bool
	hijacked    bool
}

func statusText(code int) string {
	if code == 200 {
		return "200 OK"
	}
	if code == 404 {
		return "404 Not Found"
	}
	if code == 405 {
		return "405 Method Not Allowed"
	}
	return "400 Bad Request"
}

func (w *response) WriteHeader(code int) {
	if w.hijacked || w.wroteHeader {
		return
	}
	w.wroteHeader = true
	w.conn.Write([]byte("HTTP/1.0 " + statusText(code) + "\r\n\r\n"))
}

func (w *response) Write(b []byte) (int, error) {
	if w.hijacked {
		return 0, errors.New("http: connection has been hijacked")
	}
	if !w.wroteHeader {
		w.WriteHeader(200)
	}
	return w.conn.Write(b)
}

func (w *response) Hijack() (net.Conn, error) {
	if w.hijacked {
		return nil, errors.New("http: connection has been hijacked")
	}
	w.hijacked = true
	return w.conn, nil
}

func serveConn(c net.Conn, handler Handler) {
	head, err := readHead(c)
	if err != nil {
		c.Close()
		return
	}
	method, uri, ok := parseRequestLine(head)
	w := &response{conn: c, wroteHeader: false, hijacked: false}
	if !ok {
		w.WriteHeader(400)
		c.Close()
		return
	}
	h := handler
	if h == nil {
		h = DefaultServeMux
	}
	h.ServeHTTP(w, &Request{Method: method, RequestURI: uri})
	if !w.hijacked {
		c.Close()
	}
}
