// Package echo is the basic request/response over a fresh TCP connection, the
// way a net/http client sends a request on a new connection, or grpc a unary
// call: the client dials, writes its request, and reads the reply in full
// (several Reads); the server accepts a connection, reads a fixed-size
// request in full, and writes it back.
//
// Three nodes, each a process (cmd/server, cmd/client, cmd/junk): the server
// listens at SrvAddr; the client checks that the reply is its request; the junk
// node dials the server too and writes bytes of its own. The client's check
// holds however the reads are split, whatever the junk node sends (a connection
// carries only its own dialer's bytes) and however often any node crashes (a
// crash keeps the bytes already written in flight; the restarted server listens
// again and may accept connections dialed before its crash).
package echo

import (
	"net"

	"github.com/mit-pdos/etcd-grove/examples/net/wire"
)

// SrvAddr is the server's address.
const SrvAddr = "127.0.0.1:7101"

// reqLen is the size of a request.
const reqLen = 5

// serveConn echoes one request of the connection c, then closes it.
func serveConn(c net.Conn) {
	buf := make([]byte, reqLen)
	if wire.ReadFull(c, buf) {
		c.Write(buf)
	}
	c.Close()
}

// Serve listens at SrvAddr, then accepts connections one at a time and echoes
// one request on each. It returns only if it cannot listen.
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

// Call sends the request "hello" on a new connection and checks the reply.
func Call() {
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		return
	}
	if _, err := c.Write([]byte("hello")); err != nil {
		c.Close()
		return
	}
	resp := make([]byte, reqLen)
	if wire.ReadFull(c, resp) && string(resp) != "hello" {
		panic("echo: the reply is not the request")
	}
	c.Close()
}

// SendJunk sends bytes of its own to the server.
func SendJunk() {
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		return
	}
	c.Write([]byte("xxxxxxxxxx"))
	resp := make([]byte, 3)
	wire.ReadFull(c, resp)
	c.Close()
}
