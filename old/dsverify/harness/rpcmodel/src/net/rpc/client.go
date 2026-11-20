package rpc

import (
	"errors"
	"net"
	"sync"
)

// ServerError represents an error returned by the remote side of the RPC connection (as Go's).
type ServerError string

func (e ServerError) Error() string {
	return string(e)
}

// ErrShutdown is returned by calls on a client that is shut down (as Go's).
var ErrShutdown = errors.New("connection is shut down")

var errHTTP = errors.New("unexpected HTTP response")

// connected is the server's reply to the CONNECT handshake, as Go's ("HTTP/1.0 " + connected).
const connected = "HTTP/1.0 200 Connected to Go RPC\n\n"

// pendingCall is a call waiting for its response: where its reply goes and its completion (a
// buffered channel; exactly one send).
type pendingCall struct {
	reply interface{}
	done  chan error
}

// Client is an RPC client over one connection. Go's net/rpc: client.go (send, input, Call,
// Close).
type Client struct {
	conn     net.Conn
	sending  sync.Mutex
	mu       sync.Mutex
	seq      uint64
	pending  map[uint64]*pendingCall
	closing  bool // the user called Close
	shutdown bool // the reader has stopped
}

// NewClient returns a new Client to handle requests to the set of services at the other end of
// the connection (Go's NewClient, which takes any io.ReadWriteCloser; the model's callers pass a
// net.Conn on which the HTTP CONNECT handshake is done, as DialHTTPPath's).
func NewClient(conn net.Conn) *Client {
	return newClient(conn)
}

func newClient(conn net.Conn) *Client {
	c := &Client{conn: conn, pending: make(map[uint64]*pendingCall)}
	go c.input()
	return c
}

// input reads responses and completes their calls, decoding each reply into its call's reply
// value; after an error (reading, or decoding a reply) it completes every pending call with an
// error and marks the client shut down (Go's Client.input).
func (c *Client) input() {
	var err error
	for {
		p, rerr := readFrame(c.conn)
		if rerr != nil {
			err = rerr
			break
		}
		seq, msg, body, ok := decodeMsg(p)
		if !ok {
			err = errFrame
			break
		}
		c.mu.Lock()
		pc, found := c.pending[seq]
		delete(c.pending, seq)
		c.mu.Unlock()
		if !found {
			continue
		}
		if msg != "" {
			pc.done <- ServerError(msg)
			continue
		}
		derr := getCodec().Decode(body, pc.reply)
		if derr != nil {
			pc.done <- errors.New("reading body " + derr.Error())
			err = derr
			break
		}
		pc.done <- nil
	}
	c.sending.Lock()
	c.mu.Lock()
	c.shutdown = true
	if c.closing {
		err = ErrShutdown
	}
	for _, pc := range c.pending {
		pc.done <- err
	}
	c.pending = make(map[uint64]*pendingCall)
	c.mu.Unlock()
	c.sending.Unlock()
}

// Call invokes the named function, waits for it to complete, and returns its error status. The
// arguments are encoded by the kit's codec; the reply is decoded into reply by the reader (as gob
// would).
func (c *Client) Call(serviceMethod string, args interface{}, reply interface{}) error {
	pc := &pendingCall{reply: reply, done: make(chan error, 1)}
	c.sending.Lock()
	c.mu.Lock()
	if c.shutdown || c.closing {
		c.mu.Unlock()
		c.sending.Unlock()
		return ErrShutdown
	}
	seq := c.seq
	c.seq = seq + 1
	if _, dup := c.pending[seq]; dup {
		// the sequence numbers wrapped around onto a call still pending (after 2^64 calls)
		c.mu.Unlock()
		c.sending.Unlock()
		return ErrShutdown
	}
	c.pending[seq] = pc
	c.mu.Unlock()
	err := writeFrame(c.conn, encodeMsg(seq, serviceMethod, getCodec().Encode(args)))
	if err != nil {
		// a failed write closes the connection (as every later write on a broken TCP
		// connection fails) and shuts the client down at once (as the reader will once it
		// fails): no later frame follows a partial one, and no later call reuses a sequence
		// number that a request whose write failed may still be answered with
		c.conn.Close()
		c.mu.Lock()
		c.shutdown = true
		c.mu.Unlock()
	}
	c.sending.Unlock()
	if err != nil {
		c.mu.Lock()
		_, still := c.pending[seq]
		delete(c.pending, seq)
		c.mu.Unlock()
		if still {
			return err
		}
	}
	return <-pc.done
}

// Close closes the client's connection; a second Close returns ErrShutdown.
func (c *Client) Close() error {
	c.mu.Lock()
	if c.closing {
		c.mu.Unlock()
		return ErrShutdown
	}
	c.closing = true
	c.mu.Unlock()
	return c.conn.Close()
}

// DialHTTP connects to an HTTP RPC server at the specified network address listening on the
// default HTTP RPC path.
func DialHTTP(network, address string) (*Client, error) {
	return DialHTTPPath(network, address, DefaultRPCPath)
}

// DialHTTPPath connects to an HTTP RPC server at the specified network address and path: the
// CONNECT request and the server's "200 Connected to Go RPC" reply, as Go's.
func DialHTTPPath(network, address, path string) (*Client, error) {
	conn, err := net.Dial(network, address)
	if err != nil {
		return nil, err
	}
	if _, err2 := conn.Write([]byte("CONNECT " + path + " HTTP/1.0\n\n")); err2 != nil {
		conn.Close()
		return nil, err2
	}
	resp, err3 := readFull(conn, uint64(len(connected)))
	if err3 != nil {
		conn.Close()
		return nil, err3
	}
	if string(resp) != connected {
		conn.Close()
		return nil, errHTTP
	}
	return newClient(conn), nil
}
