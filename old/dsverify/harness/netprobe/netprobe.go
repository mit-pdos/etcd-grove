// Package netprobe is the harness's probe of the `net` model (notes/harness-m2a.md): an echo
// server node and a client node that use Go's `net` literally, in the style of the targets (an
// accept loop with a goroutine per connection, deadlines from time.Now, a read loop that
// handles partial reads, errors handled by closing). M2a translated it; M2c proves it
// (harness/lean/Harness/Proof/dsverify_lab/harness/netprobe): the client node checks that the
// echo is a prefix of what it wrote, which needs the protocols of the server's address.
//
// The nodes, as the rig numbers them (cmd/client, cmd/server, rig.toml): node 0 runs
// ClientMain, node 1 runs ServerMain. The address is a constant, the rig's address of node 1.
package netprobe

import (
	"net"
	"time"
)

// ServerAddr is the server node's address: node 1 under the rig (10.77.0.(10+i)).
const ServerAddr = "10.77.0.11:7000"

// Msg is what the client node sends.
const Msg = "hello, echo"

// ServerMain is the server node's program.
func ServerMain() {
	Serve(ServerAddr)
}

// Serve listens on addr and echoes every connection until the listener fails.
func Serve(addr string) {
	l, err := net.Listen("tcp", addr)
	if err != nil {
		return
	}
	for {
		c, err := l.Accept()
		if err != nil {
			l.Close()
			return
		}
		go echo(c)
	}
}

func echo(c net.Conn) {
	buf := make([]byte, 64)
	for {
		n, err := c.Read(buf)
		if err != nil {
			c.Close()
			return
		}
		if _, err := c.Write(buf[:n]); err != nil {
			c.Close()
			return
		}
	}
}

// ClientMain is the client node's program: it pings the server and checks the echo.
func ClientMain() {
	msg := []byte(Msg)
	got := Ping(ServerAddr, msg)
	check(msg, got)
}

// Ping dials addr, writes msg and reads until it has as many bytes back (or an error).
// It returns the bytes read (nil if it could not send msg).
func Ping(addr string, msg []byte) []byte {
	c, err := net.DialTimeout("tcp", addr, time.Second)
	if err != nil {
		return nil
	}
	if err := c.SetWriteDeadline(time.Now().Add(time.Second)); err != nil {
		c.Close()
		return nil
	}
	if _, err := c.Write(msg); err != nil {
		c.Close()
		return nil
	}
	if err := c.SetReadDeadline(time.Now().Add(time.Second)); err != nil {
		c.Close()
		return nil
	}
	got := make([]byte, 0, len(msg))
	buf := make([]byte, 64)
	for len(got) < len(msg) {
		n, err := c.Read(buf)
		got = append(got, buf[:n]...)
		if err != nil {
			break
		}
	}
	c.Close()
	return got
}

// check panics unless got is a prefix of msg: the echo may be cut short (by an error or a
// timeout), but never longer or different.
func check(msg []byte, got []byte) {
	if len(got) > len(msg) {
		panic("netprobe: echo longer than the message")
	}
	for i := 0; i < len(got); i++ {
		if got[i] != msg[i] {
			panic("netprobe: echo differs from the message")
		}
	}
}
