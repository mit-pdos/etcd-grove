package grpc

import (
	"context"
	"net"
	"sync"

	"github.com/goose-lang/primitive"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/proto"
)

// Server is a gRPC server to serve RPC requests: its registered services by name.
type Server struct {
	mu       sync.Mutex
	services map[string]*serviceInfo
	serve    bool
}

// serviceInfo is a registered service: its implementation and its methods' handlers by name.
type serviceInfo struct {
	impl    interface{}
	methods map[string]MethodHandler
}

// NewServer creates a gRPC server which has no service registered (the model takes no options).
func NewServer(opt ...ServerOption) *Server {
	return &Server{services: make(map[string]*serviceInfo)}
}

// RegisterService registers a service and its implementation to the gRPC server (the real
// register): a registration after Serve or a second one of a name is fatal (the real
// logger.Fatalf, which exits; the model panics, as the lab's log model's Fatal). The real one
// also checks by reflection that impl implements sd.HandlerType; the generated
// RegisterXServer(s, srv XServer) can only pass one that does, so the model does not check. A
// descriptor with streams panics: the model serves unary methods only.
func (s *Server) RegisterService(sd *ServiceDesc, ss interface{}) {
	if len(sd.Streams) != 0 {
		panic("grpc model: streaming methods are not modeled")
	}
	s.mu.Lock()
	if s.serve {
		s.mu.Unlock()
		panic("grpc: Server.RegisterService after Server.Serve for " + sd.ServiceName)
	}
	if _, dup := s.services[sd.ServiceName]; dup {
		s.mu.Unlock()
		panic("grpc: Server.RegisterService found duplicate service registration for " + sd.ServiceName)
	}
	ms := make(map[string]MethodHandler)
	for _, d := range sd.Methods {
		ms[d.MethodName] = d.Handler
	}
	s.services[sd.ServiceName] = &serviceInfo{impl: ss, methods: ms}
	s.mu.Unlock()
}

// Serve accepts incoming connections on the listener lis and serves each, each in its own
// goroutine. After an Accept error it either retries or closes lis and returns the error: the real
// Serve retries a temporary error (after a backoff) and returns any other; the net model's Accept
// errors have an arbitrary Temporary(), so the model chooses either way for any error (an
// arbitrary choice, primitive.RandomUint64: random when run, any value in Goose's semantics),
// which covers the real behavior.
func (s *Server) Serve(lis net.Listener) error {
	s.mu.Lock()
	s.serve = true
	s.mu.Unlock()
	for {
		conn, err := lis.Accept()
		if err != nil {
			if primitive.RandomUint64()%2 == 0 {
				continue
			}
			lis.Close()
			return err
		}
		go s.serveConn(conn)
	}
}

// serverConn is a served connection: its writer (the answers, one at a time; after a failed
// write, none) and the cancel functions of its running calls by sequence number.
type serverConn struct {
	conn   net.Conn
	mu     sync.Mutex
	broken bool
	active map[uint64]context.CancelFunc
}

// serveConn reads the connection's calls and cancellations until it fails, running each call
// in its own goroutine; then cancels every running call's context and closes the connection.
func (s *Server) serveConn(conn net.Conn) {
	sc := &serverConn{conn: conn, active: make(map[uint64]context.CancelFunc)}
	for {
		p, err := readFrame(conn)
		if err != nil {
			break
		}
		tag, seq, method, body, ok := decodeMsg(p)
		if !ok {
			break
		}
		if tag == tagCancel {
			sc.cancelCall(seq)
			continue
		}
		ctx, cancel := context.WithCancel(context.Background())
		sc.mu.Lock()
		sc.active[seq] = cancel
		sc.mu.Unlock()
		go s.handle(sc, ctx, cancel, seq, method, body)
	}
	sc.mu.Lock()
	for _, c := range sc.active {
		c()
	}
	sc.active = make(map[uint64]context.CancelFunc)
	sc.mu.Unlock()
	conn.Close()
}

// cancelCall cancels the context of call seq, if it is running.
func (sc *serverConn) cancelCall(seq uint64) {
	sc.mu.Lock()
	c, ok := sc.active[seq]
	sc.mu.Unlock()
	if ok {
		c()
	}
}

// handle runs a call and writes its answer (unless the connection's writer is broken).
func (s *Server) handle(sc *serverConn, ctx context.Context, cancel context.CancelFunc, seq uint64, method string, body []byte) {
	code, msg, reply := s.call(ctx, method, body)
	cancel()
	sc.mu.Lock()
	delete(sc.active, seq)
	if !sc.broken {
		if err := writeFrame(sc.conn, encodeMsg(code, seq, msg, reply)); err != nil {
			sc.broken = true
			sc.conn.Close()
		}
	}
	sc.mu.Unlock()
}

// lastSlash is the index of the last '/' in s, or -1.
func lastSlash(s string) int {
	i := len(s) - 1
	for i >= 0 {
		if s[i] == '/' {
			return i
		}
		i = i - 1
	}
	return -1
}

// call looks up "/service/method" and runs its handler (the real handleStream, processRPC and
// wrapUnaryHandler): the status code, message and encoded reply.
func (s *Server) call(ctx context.Context, fm string, body []byte) (uint64, string, []byte) {
	if len(fm) == 0 || fm[0] != '/' {
		return uint64(codes.Unimplemented), "malformed method name: \"" + fm + "\"", nil
	}
	sm := fm[1:]
	pos := lastSlash(sm)
	if pos < 0 {
		return uint64(codes.Unimplemented), "malformed method name: \"" + fm + "\"", nil
	}
	service := sm[:pos]
	method := sm[pos+1:]
	s.mu.Lock()
	info, known := s.services[service]
	s.mu.Unlock()
	if !known {
		return uint64(codes.Unimplemented), "unknown service " + service, nil
	}
	h, found := info.methods[method]
	if !found {
		return uint64(codes.Unimplemented), "unknown method " + method + " for service " + service, nil
	}
	dec := func(v interface{}) error {
		if uint64(len(body)) > maxRecvMsgSize {
			return status.Error(codes.ResourceExhausted, "grpc: received message larger than max")
		}
		if err := proto.UnmarshalValue(body, v); err != nil {
			return status.Error(codes.Internal, "grpc: error unmarshalling request")
		}
		return nil
	}
	reply, err := h(info.impl, ctx, dec, nil)
	if err != nil {
		st, ok := status.FromError(err)
		if !ok {
			st = status.FromContextError(err)
		}
		return uint64(st.Code()), st.Message(), nil
	}
	rb, merr := encode(reply)
	if merr != nil {
		return uint64(codes.Internal), "grpc: error while marshaling", nil
	}
	if uint64(len(rb)) > maxSendMsgSize {
		return uint64(codes.ResourceExhausted), "grpc: trying to send message larger than max", nil
	}
	return uint64(codes.OK), "", rb
}
