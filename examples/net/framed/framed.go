// Package framed is several request/response exchanges on one persistent
// connection, each message length-prefixed: HTTP/1.1 keep-alive, where
// net/http's server reads request after request on one connection
// ((*conn).serve's loop, src/net/http/server.go) and its Transport reuses an
// idle persistConn (src/net/http/transport.go), and grpc's length-prefixed
// messages (a header, then the payload, both read with io.ReadFull:
// (*parser).recvMsg, grpc-go rpc_util.go). A message here is a 1-byte length
// then the payload, which the client writes as two Writes, header then payload,
// as a buffered writer's flush may split them.
//
// Three nodes: Server listens at SrvAddr and serves each connection in turn,
// echoing message after message until an error; Client sends three messages of
// different sizes on one connection and checks that each reply is its request;
// Junk dials the server too and writes malformed frames. The client's check
// holds however the bytes are split among Reads, because a connection carries
// its own dialer's bytes in order and intact: the server's n-th reply is built
// from the n-th frame of the client's stream, and the client parses the
// replies with the framing the server wrote them in. A failed write may have
// written part of its bytes, but the writer then stops (closes), so a later
// frame is never read past a partial one; Junk's bytes are on its own
// connection; a crash keeps the bytes in flight.
package framed

import (
	"net"

	"github.com/mit-pdos/etcd-grove/examples/net/wire"
)

// SrvAddr is the server's address.
const SrvAddr = "127.0.0.1:7102"

// serveConn echoes the messages of the connection c until an error, then
// closes it.
func serveConn(c net.Conn) {
	for {
		hdr := make([]byte, 1)
		if !wire.ReadFull(c, hdr) {
			break
		}
		payload := make([]byte, int(hdr[0]))
		if !wire.ReadFull(c, payload) {
			break
		}
		if _, err := c.Write(hdr); err != nil {
			break
		}
		if _, err := c.Write(payload); err != nil {
			break
		}
	}
	c.Close()
}

// Serve listens at SrvAddr, then accepts connections one at a time and serves
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

// exchange sends req as one message on c, header then payload in two Writes,
// reads the reply, and checks that it is req. It returns false on an error.
func exchange(c net.Conn, req []byte) bool {
	hdr := make([]byte, 1)
	hdr[0] = byte(len(req))
	if _, err := c.Write(hdr); err != nil {
		return false
	}
	if _, err := c.Write(req); err != nil {
		return false
	}
	rhdr := make([]byte, 1)
	if !wire.ReadFull(c, rhdr) {
		return false
	}
	resp := make([]byte, int(rhdr[0]))
	if !wire.ReadFull(c, resp) {
		return false
	}
	if string(resp) != string(req) {
		panic("framed: a reply is not its request")
	}
	return true
}

// Call sends three messages on one connection and checks each reply.
func Call() {
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		return
	}
	if exchange(c, []byte("a")) && exchange(c, []byte("bcd")) {
		exchange(c, []byte("hello"))
	}
	c.Close()
}

// SendJunk sends the server a frame whose header claims more bytes than follow,
// then closes the connection.
func SendJunk() {
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		return
	}
	c.Write([]byte("\x09xyz"))
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
