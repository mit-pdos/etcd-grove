// Package duplex is one connection used at once by a reader goroutine and a
// writer goroutine, as grpc's client transport does (the reader goroutine,
// (*http2Client).reader, and the loopyWriter goroutine, (*loopyWriter).run,
// grpc-go internal/transport/http2_client.go and controlbuf.go), and net/http's
// Transport (go pconn.readLoop() and go pconn.writeLoop() on one persistConn,
// src/net/http/transport.go).
//
// Two nodes: Server listens at SrvAddr and serves each connection in turn by
// echoing whatever it reads (io.Copy's loop, written out) until an error;
// Client dials, starts a goroutine that writes the bytes 1..N, one Write per
// byte, while its main goroutine reads N bytes one at a time and checks that
// the i-th is i. The check holds however the two goroutines interleave and
// however the server's Reads split the bytes: the bytes arrive in order and
// intact on their own connection, in both directions, and a failed write
// stops the writer (a write that fails with no deadline breaks the
// connection, which then writes nothing more), so no byte is skipped.
// Operations may fail at any time and a crash keeps the bytes in flight.
package duplex

import (
	"net"

	"github.com/mit-pdos/etcd-grove/examples/net/wire"
)

// SrvAddr is the server's address.
const SrvAddr = "127.0.0.1:7104"

// n is the number of bytes the client sends.
const n = 4

// serveConn writes back whatever it reads of the connection c until an error,
// then closes it.
func serveConn(c net.Conn) {
	buf := make([]byte, 16)
	for {
		k, err := c.Read(buf)
		if k > 0 {
			if _, werr := c.Write(buf[:k]); werr != nil {
				break
			}
		}
		if err != nil {
			break
		}
	}
	c.Close()
}

// Serve listens at SrvAddr, then accepts connections one at a time and echoes
// each until it fails. It returns only if it cannot listen.
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

// writeAll writes the bytes 1..n to c, one Write each, until one fails.
func writeAll(c net.Conn) {
	for i := 1; i <= n; i++ {
		b := make([]byte, 1)
		b[0] = byte(i)
		if _, err := c.Write(b); err != nil {
			return
		}
	}
}

// Call writes the bytes 1..n from one goroutine while it reads their echo in
// another, and checks the bytes read.
func Call() {
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		return
	}
	go writeAll(c)
	for i := 1; i <= n; i++ {
		b := make([]byte, 1)
		if !wire.ReadFull(c, b) {
			break
		}
		if b[0] != byte(i) {
			panic("duplex: a byte arrived out of order")
		}
	}
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
