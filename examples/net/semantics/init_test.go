//go:build linux

package semantics

import (
	"net"
	"testing"
)

// TestFreshProcessNoSocket (D26, the initial states). Decision: a machine's
// process starts with no listener (NetLocal.init, net_semantics's
// initLocal), and the network with no connection (NetGlobal.init, its
// initGlobal). Measured: a child started by os/exec while its parent holds
// a listener and both ends of a connection has no socket among its fds
// (Go's os/exec gives the child only its stdin, stdout and stderr, and Go
// opens every other fd close-on-exec, syscall.Socket with SOCK_CLOEXEC:
// sock_cloexec.go). The network's state before the deployment starts is
// assumed: none of its processes exists yet, and by the closed world (D13)
// no other process dials or accepts at the deployment's addresses.
// Excluded by the model: a program whose first Accept returns a connection
// no Dial of the deployment made.
func TestFreshProcessNoSocket(t *testing.T) {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	c, err := net.Dial("tcp", ln.Addr().String())
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	s, err := ln.Accept()
	if err != nil {
		t.Fatal(err)
	}
	defer s.Close()
	ch := startChild(t, "count-sockets", "")
	if n := ch.line(t); n != "0" {
		t.Fatalf("a fresh child process has %s sockets, want 0", n)
	}
}
