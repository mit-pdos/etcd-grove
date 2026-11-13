// Package preface is a handshake read under a deadline: grpc's server sets a
// deadline on each connection it accepts (SetDeadline(time.Now().Add(
// connectionTimeout)), (*Server).handleRawConn, grpc-go server.go), reads the
// client preface with io.ReadFull and checks it (NewServerTransport, grpc-go
// internal/transport/http2_server.go), closing the connection if it is wrong,
// then clears the deadline (SetDeadline(time.Time{})); the client writes the
// preface first ((*http2Client).newHTTP2Client, http2_client.go). The deadline
// is what keeps a client that never finishes its preface from holding the
// server.
//
// Three nodes: Server listens at SrvAddr and serves each connection in turn:
// it sets a deadline, reads a 4-byte preface, closes the connection if the
// preface is not Magic (no panic: junk connections happen), and otherwise
// clears the deadline and echoes a 1-byte request; Client writes Magic, then
// a 1-byte request, and checks that the reply is its request; Junk writes
// half a preface and waits. The client's check holds because its bytes arrive
// in order and intact on its own connection, so the byte the server reads
// after the preface is the client's request. A failure with a deadline set
// may be a timeout of a live connection (it does not break the connection,
// whose close then sends its FIN), so the client may see EOF instead of a
// reply, but never another byte; operations may fail at any time and a crash
// keeps the bytes in flight.
package preface

import (
	"net"
	"time"

	"github.com/mit-pdos/etcd-grove/examples/net/wire"
)

// SrvAddr is the server's address.
const SrvAddr = "127.0.0.1:7107"

// Magic is the client preface.
const Magic = "PRI*"

// prefaceLen is the length of Magic.
const prefaceLen = 4

// serveConn checks the preface of the connection c under a deadline, echoes
// one 1-byte request, and closes it.
func serveConn(c net.Conn) {
	c.SetDeadline(time.Now().Add(time.Second))
	pre := make([]byte, prefaceLen)
	if !wire.ReadFull(c, pre) || string(pre) != Magic {
		c.Close()
		return
	}
	c.SetDeadline(time.Time{})
	req := make([]byte, 1)
	if wire.ReadFull(c, req) {
		c.Write(req)
	}
	c.Close()
}

// Serve listens at SrvAddr, then accepts connections one at a time and serves
// each. It returns only if it cannot listen.
func Serve() {
	l, err := net.Listen("tcp", SrvAddr)
	if err != nil {
		return
	}
	for {
		c, err := l.Accept()
		if err != nil {
			continue
		}
		serveConn(c)
	}
}

// Call writes the preface and the request 42 on a new connection and checks
// the reply.
func Call() {
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		return
	}
	if _, err := c.Write([]byte(Magic)); err != nil {
		c.Close()
		return
	}
	req := make([]byte, 1)
	req[0] = 42
	if _, err := c.Write(req); err != nil {
		c.Close()
		return
	}
	resp := make([]byte, 1)
	if wire.ReadFull(c, resp) && resp[0] != req[0] {
		panic("preface: the reply is not the request")
	}
	c.Close()
}

// SendJunk writes half a preface, then waits for a reply (the server's
// deadline makes it give up and close the connection).
func SendJunk() {
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		return
	}
	c.Write([]byte("PR"))
	resp := make([]byte, 1)
	wire.ReadFull(c, resp)
	c.Close()
}

// Server is the server node's boot program.
func Server() {
	Serve()
	wire.Forever()
}

// Client is the client node's boot program.
func Client() {
	Call()
	wire.Forever()
}

// Junk is the third node's boot program.
func Junk() {
	SendJunk()
	wire.Forever()
}
