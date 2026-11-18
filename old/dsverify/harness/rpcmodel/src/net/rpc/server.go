package rpc

import (
	"errors"
	"net"
	"net/http"
	"sync"
)

const (
	// DefaultRPCPath is the path HandleHTTP serves RPC on (as Go's).
	DefaultRPCPath = "/_goRPC_"
	// DefaultDebugPath is Go's debugging path; the model serves nothing there.
	DefaultDebugPath = "/debug/rpc"
)

// Server represents an RPC Server: its registered receivers by service name.
type Server struct {
	mu       sync.Mutex
	services map[string]interface{}
}

// NewServer returns a new Server.
func NewServer() *Server {
	return &Server{services: make(map[string]interface{})}
}

// DefaultServer is the default instance of *Server.
var DefaultServer = NewServer()

// RegisterName publishes rcvr's methods under name (Go's Server.register with useName): an
// error if rcvr has no suitable methods or the name is taken or empty.
func (s *Server) RegisterName(name string, rcvr interface{}) error {
	if name == "" {
		return errors.New("rpc.Register: no service name for type")
	}
	if getCodec().Methods(rcvr) == 0 {
		return errors.New("rpc.Register: type has no exported methods of suitable type")
	}
	s.mu.Lock()
	_, dup := s.services[name]
	if dup {
		s.mu.Unlock()
		return errors.New("rpc: service already defined: " + name)
	}
	s.services[name] = rcvr
	s.mu.Unlock()
	return nil
}

// RegisterName publishes rcvr in the DefaultServer.
func RegisterName(name string, rcvr interface{}) error {
	return DefaultServer.RegisterName(name, rcvr)
}

// Register publishes rcvr's methods under the name of its type (Go's Server.register without
// useName): an error if the name is empty or not exported, or as RegisterName.
func (s *Server) Register(rcvr interface{}) error {
	name := getCodec().Name(rcvr)
	if name == "" {
		return errors.New("rpc.Register: no service name for type")
	}
	if name[0] < 'A' || name[0] > 'Z' {
		return errors.New("rpc.Register: type " + name + " is not exported")
	}
	return s.RegisterName(name, rcvr)
}

// Register publishes rcvr in the DefaultServer.
func Register(rcvr interface{}) error {
	return DefaultServer.Register(rcvr)
}

// HandleHTTP registers the server's HTTP handler for RPC messages on rpcPath (Go also registers
// a debugging handler on debugPath; the model does not).
func (s *Server) HandleHTTP(rpcPath, debugPath string) {
	http.Handle(rpcPath, s)
}

// HandleHTTP registers the DefaultServer's handler on DefaultRPCPath.
func HandleHTTP() {
	DefaultServer.HandleHTTP(DefaultRPCPath, DefaultDebugPath)
}

// ServeHTTP answers a CONNECT request: it takes over the connection, replies "200 Connected to
// Go RPC" and serves RPC on it (Go's Server.ServeHTTP).
func (s *Server) ServeHTTP(w http.ResponseWriter, req *http.Request) {
	if req.Method != "CONNECT" {
		w.WriteHeader(405)
		w.Write([]byte("405 must CONNECT\n"))
		return
	}
	conn, err := w.(http.Hijacker).Hijack()
	if err != nil {
		return
	}
	// A failed write closes the connection (as every later write on a broken TCP connection
	// fails): no later bytes follow a cut stream.
	if _, err2 := conn.Write([]byte(connected)); err2 != nil {
		conn.Close()
		return
	}
	s.ServeConn(conn)
}

// ServeConn serves RPC requests on conn until it fails, each in its own goroutine (Go's
// ServeCodec), then closes conn.
func (s *Server) ServeConn(conn net.Conn) {
	w := new(connWriter)
	for {
		p, err := readFrame(conn)
		if err != nil {
			break
		}
		seq, sm, body, ok := decodeMsg(p)
		if !ok {
			break
		}
		go s.serve(conn, w, seq, sm, body)
	}
	conn.Close()
}

// connWriter serializes a connection's responses: after a failed write, it writes no more (as
// every later write on a broken TCP connection fails), so no response follows a partial frame.
type connWriter struct {
	mu     sync.Mutex
	broken bool
}

func (s *Server) serve(conn net.Conn, w *connWriter, seq uint64, sm string, body []byte) {
	reply, msg := s.call(sm, body)
	w.mu.Lock()
	if !w.broken {
		if err := writeFrame(conn, encodeMsg(seq, msg, reply)); err != nil {
			w.broken = true
			conn.Close()
		}
	}
	w.mu.Unlock()
}

func lastDot(s string) int {
	i := len(s) - 1
	for i >= 0 {
		if s[i] == '.' {
			return i
		}
		i = i - 1
	}
	return -1
}

// call looks up "Service.Method" and runs it (Go's readRequestHeader and service.call).
func (s *Server) call(sm string, body []byte) ([]byte, string) {
	dot := lastDot(sm)
	if dot < 0 {
		return nil, "rpc: service/method request ill-formed: " + sm
	}
	name := sm[:dot]
	method := sm[dot+1:]
	s.mu.Lock()
	rcvr, ok := s.services[name]
	s.mu.Unlock()
	if !ok {
		return nil, "rpc: can't find service " + sm
	}
	reply, msg, found := getCodec().Call(rcvr, method, body)
	if !found {
		return nil, "rpc: can't find method " + sm
	}
	return reply, msg
}
