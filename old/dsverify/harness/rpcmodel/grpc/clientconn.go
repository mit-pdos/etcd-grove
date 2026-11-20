package grpc

import (
	"context"
	"errors"
	"net"
	"sync"

	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/proto"
)

// errNoTransportSecurity is the real Dial's error without transport credentials.
var errNoTransportSecurity = errors.New("grpc: no transport security set (use grpc.WithTransportCredentials(insecure.NewCredentials()) explicitly or set credentials)")

// ClientConn represents a virtual connection to a conceptual endpoint, to perform RPCs. The
// model's: the target's address and the current connection (a transport), made at the first
// call and again after it broke.
type ClientConn struct {
	target string
	mu     sync.Mutex
	t      *transport // nil, or the current transport (possibly shut down)
	closed bool
}

// Dial creates a client connection to the given target, without connecting (as the real
// non-blocking Dial): an error only without transport credentials.
func Dial(target string, opts ...DialOption) (*ClientConn, error) {
	return newClientConn(target, opts)
}

// DialContext is Dial (the context only bounds a blocking dial, which the model does not do).
func DialContext(ctx context.Context, target string, opts ...DialOption) (*ClientConn, error) {
	return newClientConn(target, opts)
}

// NewClient is Dial (the model's targets are "host:port" addresses, which the real NewClient
// resolves with its dns resolver to the same address).
func NewClient(target string, opts ...DialOption) (*ClientConn, error) {
	return newClientConn(target, opts)
}

func newClientConn(target string, opts []DialOption) (*ClientConn, error) {
	creds := false
	for _, o := range opts {
		if o.creds {
			creds = true
		}
	}
	if !creds {
		return nil, errNoTransportSecurity
	}
	return &ClientConn{target: target}, nil
}

// getTransport returns the current transport if it is live, else dials a new one: a status
// error Unavailable if the dial fails, Canceled after Close.
func (cc *ClientConn) getTransport() (*transport, error) {
	cc.mu.Lock()
	if cc.closed {
		cc.mu.Unlock()
		return nil, status.Error(codes.Canceled, "grpc: the client connection is closing")
	}
	t := cc.t
	if t != nil && !t.isShutdown() {
		cc.mu.Unlock()
		return t, nil
	}
	conn, err := net.Dial("tcp", cc.target)
	if err != nil {
		cc.mu.Unlock()
		return nil, status.Error(codes.Unavailable, "connection error: dial failed")
	}
	t2 := newTransport(conn)
	cc.t = t2
	cc.mu.Unlock()
	return t2, nil
}

// Invoke sends the RPC request on the wire and returns after the response is received (see the
// package doc for what it may return).
func (cc *ClientConn) Invoke(ctx context.Context, method string, args interface{}, reply interface{}, opts ...CallOption) error {
	if ctx.Err() != nil {
		return ctxErr(ctx)
	}
	req, merr := encode(args)
	if merr != nil {
		return merr
	}
	if uint64(len(req)) > maxSendMsgSize {
		return status.Error(codes.ResourceExhausted, "grpc: trying to send message larger than max")
	}
	t, terr := cc.getTransport()
	if terr != nil {
		return terr
	}
	pc, seq, ok := t.send(method, req)
	if !ok {
		return status.Error(codes.Unavailable, "transport is closing")
	}
	select {
	case r := <-pc.done:
		if r == nil {
			return status.Error(codes.Unavailable, "transport is closing")
		}
		if r.code != uint64(codes.OK) {
			return status.Error(codes.Code(r.code), r.msg)
		}
		if uint64(len(r.body)) > maxRecvMsgSize {
			return status.Error(codes.ResourceExhausted, "grpc: received message larger than max")
		}
		if uerr := proto.UnmarshalValue(r.body, reply); uerr != nil {
			return status.Error(codes.Internal, "grpc: failed to unmarshal the received message")
		}
		return nil
	case <-ctx.Done():
		t.cancel(seq)
		return ctxErr(ctx)
	}
}

// encode is the real encode: a nil message (not a typed nil pointer) is the empty message; else
// the codec's encoding, or a status error Internal.
func encode(msg interface{}) ([]byte, error) {
	if msg == nil {
		return nil, nil
	}
	b, err := proto.MarshalValue(msg)
	if err != nil {
		return nil, status.Error(codes.Internal, "grpc: error while marshaling")
	}
	return b, nil
}

// ctxErr is the status error of a done context (the real toRPCErr of ctx.Err()).
func ctxErr(ctx context.Context) error {
	if ctx.Err() == context.DeadlineExceeded {
		return status.Error(codes.DeadlineExceeded, "context deadline exceeded")
	}
	return status.Error(codes.Canceled, "context canceled")
}

// Close tears down the ClientConn and its transport: pending and later calls fail (later ones
// with Canceled); a second Close returns a status error Canceled (as the real
// ErrClientConnClosing).
func (cc *ClientConn) Close() error {
	cc.mu.Lock()
	if cc.closed {
		cc.mu.Unlock()
		return status.Error(codes.Canceled, "grpc: the client connection is closing")
	}
	cc.closed = true
	t := cc.t
	cc.t = nil
	cc.mu.Unlock()
	if t != nil {
		t.conn.Close()
	}
	return nil
}

// response is a call's answer: the status code, the status message, the encoded reply.
type response struct {
	code uint64
	msg  string
	body []byte
}

// pendingCall is a call waiting for its answer (a buffered channel; at most one send: the
// answer, or nil when the transport fails).
type pendingCall struct {
	done chan *response
}

// transport is one connection of a ClientConn, as net/rpc's model's Client: a sequence number
// per call, the pending calls, a reader goroutine (input).
type transport struct {
	conn     net.Conn
	sending  sync.Mutex
	mu       sync.Mutex
	seq      uint64
	pending  map[uint64]*pendingCall
	shutdown bool
}

func newTransport(conn net.Conn) *transport {
	t := &transport{conn: conn, pending: make(map[uint64]*pendingCall)}
	go t.input()
	return t
}

func (t *transport) isShutdown() bool {
	t.mu.Lock()
	s := t.shutdown
	t.mu.Unlock()
	return s
}

// send registers a call and writes its request: (the call, its sequence number, true), or false
// if the transport is shut down or the write fails (the call is then not pending). The client's
// frames (calls and cancellations) are numbered in the order written, from 0: a call's sequence
// number is its frame's number, so no two calls of a transport share one; a transport that has
// written 2^64-1 frames writes no more (it shuts down; unreachable in practice).
func (t *transport) send(method string, req []byte) (*pendingCall, uint64, bool) {
	pc := &pendingCall{done: make(chan *response, 1)}
	t.sending.Lock()
	t.mu.Lock()
	if t.shutdown || t.seq == maxSeq {
		t.shutdown = true
		t.mu.Unlock()
		t.sending.Unlock()
		return nil, 0, false
	}
	seq := t.seq
	t.seq = seq + 1
	t.pending[seq] = pc
	t.mu.Unlock()
	err := writeFrame(t.conn, encodeMsg(tagCall, seq, method, req))
	if err != nil {
		// a failed write closes the connection and shuts the transport down at once: no later
		// frame follows a partial one
		t.conn.Close()
		t.mu.Lock()
		t.shutdown = true
		t.mu.Unlock()
	}
	t.sending.Unlock()
	if err != nil {
		t.mu.Lock()
		_, still := t.pending[seq]
		delete(t.pending, seq)
		t.mu.Unlock()
		if still {
			return nil, 0, false
		}
	}
	return pc, seq, true
}

// cancel tells the server that the caller gave call seq up (a cancellation frame, numbered as
// the calls' frames), as the real client resets the call's stream. The call stays pending: its
// answer, if one comes, goes to its channel, which nobody reads.
func (t *transport) cancel(seq uint64) {
	t.sending.Lock()
	t.mu.Lock()
	if t.shutdown || t.seq == maxSeq {
		t.shutdown = true
		t.mu.Unlock()
		t.sending.Unlock()
		return
	}
	t.seq = t.seq + 1
	t.mu.Unlock()
	if err := writeFrame(t.conn, encodeMsg(tagCancel, seq, "", nil)); err != nil {
		t.conn.Close()
		t.mu.Lock()
		t.shutdown = true
		t.mu.Unlock()
	}
	t.sending.Unlock()
}

// input reads answers and completes their calls; after an error it shuts the transport down and
// completes every pending call with nil.
func (t *transport) input() {
	for {
		p, rerr := readFrame(t.conn)
		if rerr != nil {
			break
		}
		code, seq, msg, body, ok := decodeMsg(p)
		if !ok {
			break
		}
		t.mu.Lock()
		pc, found := t.pending[seq]
		delete(t.pending, seq)
		t.mu.Unlock()
		if found {
			pc.done <- &response{code: code, msg: msg, body: body}
		}
	}
	t.conn.Close()
	t.sending.Lock()
	t.mu.Lock()
	t.shutdown = true
	for _, pc := range t.pending {
		pc.done <- nil
	}
	t.pending = make(map[uint64]*pendingCall)
	t.mu.Unlock()
	t.sending.Unlock()
}
