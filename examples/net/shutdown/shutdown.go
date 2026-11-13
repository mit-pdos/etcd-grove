// Package shutdown is a server shut down while its accept loop is blocked, and
// a connection closed while another goroutine is blocked reading it: net/http's
// (*Server).Shutdown and grpc's (*Server).GracefulStop and Stop close the
// listeners (closeListenersLocked, src/net/http/server.go and grpc-go
// server.go), which makes the accept loop's blocked Accept return an error, on
// which Serve returns; grpc's (*http2Client).Close and net/http's
// (*persistConn).closeLocked close a connection whose reader goroutine is
// blocked in Read (grpc-go internal/transport/http2_client.go,
// src/net/http/transport.go).
//
// One node: Run listens at Addr, starts an accept loop in a goroutine (it
// closes what it accepts, and exits on Accept's first error), dials its own
// listener, starts a goroutine reading the connection until an error, closes
// the connection and checks that a Write, a Read and a second Close of it all
// fail; then closes the listener and checks that an Accept on it fails. The
// checks are Go's guarantees, which the semantics states: once Close has been
// called on a connection or a listener (whatever Close returned), every later
// operation on it fails.
package shutdown

import (
	"net"

	"github.com/mit-pdos/etcd-grove/examples/net/wire"
)

// Addr is the node's listening address.
const Addr = "127.0.0.1:7106"

// acceptLoop accepts connections on l and closes each, until Accept fails.
func acceptLoop(l net.Listener) {
	for {
		c, err := l.Accept()
		if err != nil {
			return
		}
		c.Close()
	}
}

// readLoop reads c until an error.
func readLoop(c net.Conn) {
	buf := make([]byte, 1)
	for {
		if _, err := c.Read(buf); err != nil {
			return
		}
	}
}

// closeConn closes c, then checks that a Write, a Read and a Close of it fail.
func closeConn(c net.Conn) {
	c.Close()
	buf := make([]byte, 1)
	if _, err := c.Write(buf); err == nil {
		panic("shutdown: a Write after Close succeeded")
	}
	if _, err := c.Read(buf); err == nil {
		panic("shutdown: a Read after Close succeeded")
	}
	if err := c.Close(); err == nil {
		panic("shutdown: a second Close succeeded")
	}
}

// Run listens at Addr with an accept loop, closes a connection read by another
// goroutine, then closes the listener, checking that the operations after each
// Close fail.
func Run() {
	l, err := net.Listen("tcp", Addr)
	if err != nil {
		return
	}
	go acceptLoop(l)
	c, err := net.Dial("tcp", Addr)
	if err == nil {
		go readLoop(c)
		closeConn(c)
	}
	l.Close()
	if _, err := l.Accept(); err == nil {
		panic("shutdown: an Accept after Close succeeded")
	}
}

// Node is the node's boot program.
func Node() {
	Run()
	wire.Forever()
}
