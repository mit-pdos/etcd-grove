// Package acceptloop is a server whose accept loop serves each connection in a
// goroutine of its own, as net/http's (*Server).Serve does (go c.serve(connCtx),
// src/net/http/server.go) and grpc's (*Server).Serve (a goroutine running
// handleRawConn per accepted connection, grpc-go server.go), with clients
// calling concurrently, each on its own connection.
//
// Two nodes, each a process (cmd/server, cmd/client): the server listens at
// SrvAddr and, for each connection it accepts, starts a goroutine that reads a
// 1-byte request, writes it back and closes the connection; the client starts
// 1 to maxCallers goroutines (their number drawn at random), each dialing its
// own connection, sending its own id (1, 2, ...) and checking that the reply is
// its id. The check holds however the goroutines
// of both nodes interleave: a connection carries only its own dialer's bytes,
// and the server's handler for a connection reads and writes only that
// connection, so no reply crosses to the other client. Operations may fail at
// any time (a client then gives up) and a crash keeps the bytes in flight.
package acceptloop

import (
	"net"
	"sync"

	"github.com/mit-pdos/etcd-grove/examples/net/wire"
)

// SrvAddr is the server's address.
const SrvAddr = "127.0.0.1:7103"

// maxCallers is the most concurrent calls the client makes.
const maxCallers = 8

// handle echoes one 1-byte request of the connection c, then closes it.
func handle(c net.Conn) {
	buf := make([]byte, 1)
	if wire.ReadFull(c, buf) {
		c.Write(buf)
	}
	c.Close()
}

// Serve listens at SrvAddr, then accepts connections and serves each in a
// goroutine of its own. It returns only if it cannot listen.
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
		go handle(c)
	}
}

// CallOne sends id on a new connection and checks that the reply is id.
func CallOne(id byte) {
	c, err := net.Dial("tcp", SrvAddr)
	if err != nil {
		return
	}
	req := make([]byte, 1)
	req[0] = id
	if _, err := c.Write(req); err != nil {
		c.Close()
		return
	}
	resp := make([]byte, 1)
	if wire.ReadFull(c, resp) && resp[0] != id {
		panic("acceptloop: the reply is another client's")
	}
	c.Close()
}

// Call starts 1 to maxCallers concurrent calls, their number drawn at random,
// with the distinct ids 1, 2, ..., and waits for them.
func Call() {
	m := 1 + wire.RandomInt(maxCallers-1)
	var wg sync.WaitGroup
	wg.Add(m)
	for i := 1; i <= m; i++ {
		id := byte(i)
		go func() {
			CallOne(id)
			wg.Done()
		}()
	}
	wg.Wait()
}
