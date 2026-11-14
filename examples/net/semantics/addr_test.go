//go:build linux

package semantics

import (
	"net"
	"strconv"
	"testing"
)

// TestAddressAliases (D12: "the plan's strings must name distinct sockets (no
// two strings for one host:port)"; D7: a listener at a accepts only
// connections dialed to the string a). Distinct strings reach one listener:
// a listener at "127.0.0.1:P" accepts Dials of "localhost:P" and of ":P"
// (Go: an empty host dials the local system); a wildcard listener at ":P"
// accepts a Dial of "127.0.0.1:P" and "127.0.0.2:P" (all of 127/8 is local);
// and with ":P" listened, Listen of "127.0.0.1:P" fails (EADDRINUSE). Linux
// routes by the bound address and port, Go resolves names: what D12 excludes
// is wider than "two strings for one host:port" (":P" and "127.0.0.1:P" are
// different host:port pairs and conflict, and the wildcard catches every
// local address), so a plan with two such strings is a deployment D12 must
// exclude explicitly (notes/axiom-review/tcp-semantics.md). Measured.
func TestAddressAliases(t *testing.T) {
	t.Parallel()
	accepts := func(ln net.Listener, dial string) bool {
		c, err := net.Dial("tcp", dial)
		if err != nil {
			t.Logf("Dial(%q): %v", dial, err)
			return false
		}
		defer c.Close()
		a, err := ln.Accept()
		if err != nil {
			return false
		}
		defer a.Close()
		return a.LocalAddr().String() == c.RemoteAddr().String()
	}
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	defer ln.Close()
	p := strconv.Itoa(ln.Addr().(*net.TCPAddr).Port)
	for _, s := range []string{"localhost:" + p, ":" + p} {
		if !accepts(ln, s) {
			t.Errorf("listener at 127.0.0.1:%s did not accept a Dial of %q", p, s)
		}
	}
	ln.Close()

	w, err := net.Listen("tcp", ":0")
	if err != nil {
		t.Fatal(err)
	}
	defer w.Close()
	q := strconv.Itoa(w.Addr().(*net.TCPAddr).Port)
	for _, s := range []string{"127.0.0.1:" + q, "127.0.0.2:" + q} {
		if !accepts(w, s) {
			t.Errorf("listener at :%s did not accept a Dial of %q", q, s)
		}
	}
	if l2, err := net.Listen("tcp", "127.0.0.1:"+q); err == nil {
		l2.Close()
		t.Errorf("Listen(127.0.0.1:%s) with :%s listened succeeded; want EADDRINUSE", q, q)
	} else if name(err) != "EADDRINUSE" {
		t.Errorf("Listen(127.0.0.1:%s) with :%s listened: %v; want EADDRINUSE", q, q, err)
	}
}
