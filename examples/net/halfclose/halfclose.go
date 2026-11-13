// Package halfclose is a request ended by shutting the connection's write side
// (CloseWrite, a TCP FIN) and a response read until EOF: net/http's server
// ends a connection with closeWriteAndWait (a type assertion of the connection
// to its closeWriter interface, which *net.TCPConn implements, then
// CloseWrite; src/net/http/server.go), and a response with neither a
// Content-Length nor chunking is delimited by the connection's close, its body
// read until EOF (readTransfer, src/net/http/transfer.go).
//
// Two nodes: Server listens at SrvAddr and serves each connection in turn: it
// reads until EOF, writes everything it read back, and closes the connection;
// Client dials, writes its request, shuts its write side, reads until EOF and
// checks that the response is exactly its request. The check holds because a
// reader sees EOF only after every byte in flight and the writer's FIN, and a
// writer sends its FIN only if its writes all succeeded (a write that fails
// with no deadline breaks the connection, whose close then sends no FIN): so
// the server's EOF means it has read all of the request and nothing more, and
// the client's means it has read all of the server's single write. Reads may
// return any number of bytes, operations may fail at any time (no EOF then),
// and a crash keeps the bytes in flight but sends no FIN.
package halfclose

import (
	"io"
	"net"

	"github.com/mit-pdos/etcd-grove/examples/net/wire"
)

// SrvAddr is the server's address.
const SrvAddr = "127.0.0.1:7105"

// readAll reads c until EOF. It returns the bytes read, and whether EOF was
// reached (false: an error).
func readAll(c net.Conn) ([]byte, bool) {
	var data []byte
	buf := make([]byte, 8)
	for {
		k, err := c.Read(buf)
		data = append(data, buf[:k]...)
		if err == io.EOF {
			return data, true
		}
		if err != nil {
			return data, false
		}
	}
}

// serveConn reads the connection c until EOF, writes back what it read, and
// closes it.
func serveConn(c net.Conn) {
	req, ok := readAll(c)
	if ok {
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

// Call sends the request "hello", shuts its write side, and checks that the
// response read until EOF is the request.
func Call() {
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		return
	}
	if _, err := c.Write([]byte("hello")); err != nil {
		c.Close()
		return
	}
	if err := c.(*net.TCPConn).CloseWrite(); err != nil {
		c.Close()
		return
	}
	resp, ok := readAll(c)
	if ok && string(resp) != "hello" {
		panic("halfclose: the response is not the request")
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
