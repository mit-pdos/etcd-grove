// Package tcpsquat shows that the TCP extension's results rest on a
// deployment assumption no theorem states (notes/axiom-review/tcp-semantics.md,
// "The closed world"): that no process outside the system listens at a plan
// address. examples/net/echo's echo_crash_safety says that echo's client never
// panics; here a process that is not one of echo's nodes listens at echo's
// SrvAddr before the server does (the server's Listen then fails, which the
// semantics allows), and the client, run as echo runs it, connects to it and
// panics. In the semantics only a node of the system, at the plan's host, can
// Listen at SrvAddr (D6) and accept the client's connection (D7).
package tcpsquat

import (
	"net"
	"testing"

	"github.com/mit-pdos/etcd-grove/examples/net/echo"
)

func TestSquatterMakesEchoClientPanic(t *testing.T) {
	sq, err := net.Listen("tcp", echo.SrvAddr)
	if err != nil {
		t.Fatalf("squatter's Listen: %v", err)
	}
	defer sq.Close()
	go func() {
		for {
			c, err := sq.Accept()
			if err != nil {
				return
			}
			c.Write([]byte("jello"))
			c.Close()
		}
	}()
	go echo.Serve() // returns at once: its Listen fails (EADDRINUSE)
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("echo.Call returned without panicking")
		}
		t.Logf("echo.Call panicked: %v", r)
	}()
	echo.Call()
}
